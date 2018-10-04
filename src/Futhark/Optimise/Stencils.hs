{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Perform stencil optimisation.
module Futhark.Optimise.Stencils ( optimiseStencils ) where
import Debug.Trace
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Data.Either
import qualified Data.Map.Strict as M
import Data.Semigroup ((<>))
import Data.List
import Data.Maybe

import Futhark.MonadFreshNames
import Futhark.Representation.Kernels
import Futhark.Pass
import Futhark.Tools

import Prelude

optimiseStencils :: Pass Kernels Kernels
optimiseStencils = Pass "optimise stencils" "Optimise kernels with stencil-like memory access patterns" $
                   intraproceduralTransformation optimiseFunDef

optimiseFunDef :: MonadFreshNames m => FunDef Kernels -> m (FunDef Kernels)
optimiseFunDef fundec = do
  body' <- modifyNameSource $ runState $
           runReaderT (runTileM m) (scopeOfFParams (funDefParams fundec))
  return fundec { funDefBody = body' }
  where m = optimiseBody $ funDefBody fundec

newtype TileM a = TileM { runTileM :: ReaderT (Scope Kernels) (State VNameSource) a }
  deriving (Functor, Applicative, Monad,
            HasScope Kernels, LocalScope Kernels, MonadFreshNames)

optimiseBody :: Body Kernels -> TileM (Body Kernels)
optimiseBody (Body () bnds res) =
  Body () <$> (mconcat <$> mapM optimiseStm (stmsToList bnds)) <*> pure res

optimiseStm :: Stm Kernels -> TileM (Stms Kernels)
optimiseStm (Let pat aux (Op old_kernel@(Kernel desc space ts body))) = do
  (extra_stms, space', body') <- optimiseKernelBody space body
  let new_kernel = Kernel desc space' ts body'
  -- XXX: we should not change the type of the kernel (such as by
  -- changing the number of groups being used for a kernel that
  -- returns a result-per-group).
  if kernelType old_kernel == kernelType new_kernel
    then return $ extra_stms <> oneStm (Let pat aux $ Op new_kernel)
    else return $ oneStm $ Let pat aux $ Op old_kernel
optimiseStm (Let pat aux e) =
  pure <$> (Let pat aux <$> mapExpM optimise e)
  where optimise = identityMapper { mapOnBody = \scope -> localScope scope . optimiseBody }

optimiseKernelBody :: KernelSpace -> KernelBody InKernel
                   -> TileM (Stms Kernels, KernelSpace, KernelBody InKernel)
optimiseKernelBody kspace (KernelBody () kstms kres) = do
  scope <- askScope
  let outer_vtable = M.mapMaybeWithKey fromOuter (scopeOfKernelSpace kspace <> scope)
      vtable = primExpTable outer_vtable kstms
      gtids = map fst $ spaceDimensions kspace
  case detectStencil $
       findCandidateIndexing (fmap typeOf . (`M.lookup` scope)) gtids vtable kstms of

    Stencil1D stencils -> do
      kstms' <- oneDimensionalStencil scope kspace kstms stencils
      return (mempty, kspace, KernelBody () kstms' kres)

    Stencil2D stencils
      | FlatThreadSpace gspace <- spaceStructure kspace -> do

      ((kspace', (ltid_d1, ltid_d2), tile_size), kspace_stms) <- runBinder $ do
        tile_size_key <- newVName "tile_size"
        tile_size <- letSubExp "tile_size" $ Op $ GetSize tile_size_key SizeTile
        tiled_group_size <- letSubExp "tiled_group_size" $
                            BasicOp $ BinOp (Mul Int32) tile_size tile_size

        let (tiled_gspace,untiled_gspace) = splitAt 2 $ reverse gspace
        -- Play with reversion to ensure we get increasing IDs for
        -- ltids.  This affects readability of generated code.
        untiled_gspace' <- fmap reverse $ forM (reverse untiled_gspace) $ \(gtid,gdim) -> do
          ltid <- newVName "ltid"
          return (gtid,gdim,
                  ltid, constant (1::Int32))
        tiled_gspace' <- fmap reverse $ forM (reverse tiled_gspace) $ \(gtid,gdim) -> do
          ltid <- newVName "ltid"
          return (gtid,gdim,
                  ltid, tile_size)
        let gspace' = reverse $ tiled_gspace' ++ untiled_gspace'

        -- We have to recalculate number of workgroups and
        -- number of threads to fit the new workgroup size.
        (num_threads, num_groups) <- sufficientGroups gspace' tiled_group_size

        let [(_, _, ltid_d1, _), (_, _, ltid_d2, _)] = tiled_gspace'
        return (kspace { spaceStructure = NestedThreadSpace gspace'
                       , spaceGroupSize = tiled_group_size
                       , spaceNumThreads = num_threads
                       , spaceNumGroups = num_groups
                       },
                (ltid_d1, ltid_d2),
                tile_size)

      kstms' <- twoDimensionalStencil scope tile_size
                ltid_d1 ltid_d2 kspace' kstms stencils

      return (kspace_stms, kspace', KernelBody () kstms' kres)
    _ -> return (mempty, kspace, KernelBody () kstms kres)

  where fromOuter k info = case typeOf info of Prim pt -> Just $ LeafExp k pt
                                               _       -> Nothing

oneDimensionalStencil :: Scope Kernels
                      -> KernelSpace -> Stms InKernel -> [Stencil1DPart] -> TileM (Stms InKernel)
oneDimensionalStencil scope kspace kstms stencils =
  fmap snd $ flip runBinderT (scopeOfKernelSpace kspace <> castScope scope) $ do
  let halo_size = foldl' max 0 $ map unOffset $
                  concatMap indexingOffset $ concatMap (stencilIndexings oneDoffset) stencils
  stencil_size <- letSubExp "stencil_size" $
                  BasicOp $ BinOp (Add Int32) (spaceGroupSize kspace) (constant $ halo_size * 2)
  ctid <- newVName "ctid"
  let cspace = combineSpace [(ctid, stencil_size)]
      arrs = nub $ map stencilArray stencils
  arr_ts <- mapM lookupType arrs

  readElems <- fmap (uncurry $ flip mkBody) $ runBinder $
               forM (zip arrs arr_ts) $ \(arr, arr_t) -> do
    offset <- letSubExp "offset" $ BasicOp $
              BinOp (Mul Int32) (Var (spaceGroupId kspace)) (spaceGroupSize kspace)
    i_offbyhalo <- letSubExp "i_offbyhalo" $ BasicOp $ BinOp (Add Int32) offset (Var ctid)
    i_oob <- letSubExp "i_oob" $ BasicOp $ BinOp (Sub Int32) i_offbyhalo (constant halo_size)
    i <- letSubExp "i" $ BasicOp $ BinOp (SMod Int32) i_oob (arraySize 0 arr_t)
    letSubExp (baseString arr <> "_elem") $ BasicOp $ Index arr $
      fullSlice arr_t [DimFix i]

  stencil_chunks <- letTupExp "stencil_chunk" $ Op $
    Combine cspace (map (Prim . elemType) arr_ts) [] readElems

  let indexes = concatMap (stencilIndexings oneDoffset) stencils
      replace pe = do
        Indexing _ orig_arr [Offset k] <- find ((==pe) . indexingPatElem) indexes
        arr <- lookup orig_arr $ zip arrs stencil_chunks
        return $ do
          new_index <- letSubExp "stencil_new_index" $ BasicOp $
                       BinOp (Add Int32) (Var $ spaceLocalId kspace) $
                       constant $ k + halo_size
          return (arr, [DimFix new_index])

  mapM_ addStm =<< replaceIndexing replace kstms

twoDimensionalStencil :: Scope Kernels -> SubExp
                      -> VName -> VName -> KernelSpace -> Stms InKernel -> [Stencil2DPart]
                      -> TileM (Stms InKernel)
twoDimensionalStencil scope tile_size ltid_d1 ltid_d2 kspace kstms stencils =
  fmap snd $ flip runBinderT (scopeOfKernelSpace kspace <> castScope scope) $ do
  let halo_size_d1 = foldl' max 0 $ map (unOffset . fst) $
                     concatMap stencilOffsets stencils
      halo_size_d2 = foldl' max 0 $ map (unOffset . snd) $
                     concatMap stencilOffsets stencils
  stencil_size_d1 <- letSubExp "stencil_size_d1" $
                     BasicOp $ BinOp (Add Int32) tile_size (constant $ halo_size_d1 * 2)
  stencil_size_d2 <- letSubExp "stencil_size_d2" $
                     BasicOp $ BinOp (Add Int32) tile_size (constant $ halo_size_d2 * 2)
  ctid_d1 <- newVName "ctid_d1"
  ctid_d2 <- newVName "ctid_d2"
  let cspace = combineSpace [(ctid_d1, stencil_size_d1), (ctid_d2, stencil_size_d2)]
      arrs = nub $ map stencilArray stencils
  arr_ts <- mapM lookupType arrs

  let newIndex arr_t ctid halo_size = do
        offset <- letSubExp "offset" $ BasicOp $
          BinOp (Mul Int32) (Var (spaceGroupId kspace)) tile_size
        i_offbyhalo <- letSubExp "i_offbyhalo" $ BasicOp $ BinOp (Add Int32) offset (Var ctid)
        i_oob <- letSubExp "i_oob" $ BasicOp $ BinOp (Sub Int32) i_offbyhalo (constant halo_size)
        letSubExp "i" $ BasicOp $ BinOp (SMod Int32) i_oob (arraySize 0 arr_t)

  readElems <- fmap (uncurry $ flip mkBody) $ runBinder $
               forM (zip arrs arr_ts) $ \(arr, arr_t) -> do
    i <- newIndex arr_t ctid_d1 halo_size_d1
    j <- newIndex arr_t ctid_d2 halo_size_d2
    letSubExp (baseString arr <> "_elem") $ BasicOp $ Index arr $
      fullSlice arr_t [DimFix i, DimFix j]

  stencil_chunks <- letTupExp "stencil_chunk" $ Op $
    Combine cspace (map (Prim . elemType) arr_ts) [] readElems

  let indexes = concatMap (stencilIndexings twoDoffset) stencils
      replace pe = do
        Indexing _ orig_arr [Offset k1, Offset k2] <- find ((==pe) . indexingPatElem) indexes
        arr <- lookup orig_arr $ zip arrs stencil_chunks
        return $ do
          i <- letSubExp "stencil_new_index_d1" $ BasicOp $
               BinOp (Add Int32) (Var ltid_d1) $
               constant $ k1 + halo_size_d1
          j <- letSubExp "stencil_new_index_d1" $ BasicOp $
               BinOp (Add Int32) (Var ltid_d2) $
               constant $ k2 + halo_size_d2
          return (arr, [DimFix i, DimFix j])

  mapM_ addStm =<< replaceIndexing replace kstms

primExpTable :: M.Map VName (PrimExp v)
             -> Stms InKernel
             -> M.Map VName (PrimExp v)
primExpTable = foldl' bindsOne
  where bindsOne vtable stm =
          case patternNames $ stmPattern stm of
            [v] | Just pe <- primExpFromExp (`M.lookup` vtable) $ stmExp stm ->
                    M.insert v pe vtable
            _   -> vtable

newtype Offset = Offset { unOffset :: Int32 }
               deriving (Show, Eq, Ord)

oneDoffset :: Offset -> [Offset]
oneDoffset = pure

twoDoffset :: (Offset, Offset) -> [Offset]
twoDoffset (i, j) = [i, j]

data StencilPart offset = StencilPart { stencilArray :: VName
                                      , stencilArea :: [(offset, PatElem InKernel)]
                                      }
                        deriving (Show)

stencilOffsets :: StencilPart offset -> [offset]
stencilOffsets = map fst . stencilArea

stencilIndexings :: (offset -> [Offset]) -> StencilPart offset -> [Indexing]
stencilIndexings f (StencilPart arr area) = do
  (offset, pe) <- area
  return $ Indexing pe arr $ f offset

type Stencil1DPart = StencilPart Offset
type Stencil2DPart = StencilPart (Offset, Offset)

data Stencil = Stencil1D [Stencil1DPart]
             | Stencil2D [Stencil2DPart]
             | NoStencil
             deriving (Show)

data Indexing = Indexing { indexingPatElem :: PatElem InKernel
                         , indexingArray :: VName
                         , indexingOffset :: [Offset]
                         }
              deriving (Show)

detectStencil :: [Indexing] -> Stencil
detectStencil [] = NoStencil
detectStencil (indexing1 : indexings)
  | length (indexingOffset indexing1) == 1,
    Just (area, indexings') <- isStencil oneD =
      case detectStencil indexings' of
        NoStencil -> Stencil1D [StencilPart (indexingArray indexing1) area]
        Stencil1D stencils -> Stencil1D $ StencilPart (indexingArray indexing1) area : stencils
        Stencil2D stencils -> Stencil2D $ oneDtoTwoD (StencilPart (indexingArray indexing1) area) : stencils
  | length (indexingOffset indexing1) == 2,
    Just (area, indexings') <- isStencil twoD =
      case detectStencil indexings' of
        NoStencil -> Stencil2D [StencilPart (indexingArray indexing1) area]
        Stencil1D stencils -> Stencil2D $ StencilPart (indexingArray indexing1) area : map oneDtoTwoD stencils
        Stencil2D stencils -> Stencil2D $ StencilPart (indexingArray indexing1) area : stencils
  | otherwise =
      detectStencil indexings
  where isStencil :: (Indexing -> Maybe a) -> Maybe ([(a, PatElemT Type)], [Indexing])
        isStencil stencil =
          let (area, indexings') = partitionEithers $ map (partOfStencil stencil) $ indexing1 : indexings
          in if length area > 1 then Just (area, indexings') else Nothing

        oneD indexing2
          | [i] <- indexingOffset indexing2 = Just i
          | otherwise = Nothing
        twoD indexing2
          | [i,j] <- indexingOffset indexing2 = Just (i, j)
          | otherwise = Nothing

        partOfStencil :: (Indexing -> Maybe a) -> Indexing -> Either (a, PatElemT Type) Indexing
        partOfStencil stencil indexing2
          | indexingArray indexing2 == indexingArray indexing1,
            Just is <- stencil indexing2 =
              Left (is, indexingPatElem indexing2)
          | otherwise =
              Right indexing2

        oneDtoTwoD (StencilPart arr area) =
          StencilPart arr $ do (i, pe) <- area
                               return ((Offset 0, i), pe)

isOffset :: SubExp -> VName -> PrimExp VName -> Maybe Offset
isOffset d tid e
  | Just k <- tidMod e = Just k
  | Just k <- tidOffset e = Just k
  | isTid e = Just $ Offset 0
  | otherwise = Nothing
  where isTid (LeafExp x _) | x == tid = True
        isTid _ = False

        tidOffset (BinOpExp (Add Int32)
                   (ValueExp (IntValue (Int32Value k))) x)
          | isTid x, k `elem` [-2..2] = Just $ Offset k
        tidOffset (BinOpExp (Sub Int32)
                   x (ValueExp (IntValue (Int32Value k))))
          | isTid x, k `elem` [-2..2] = Just $ Offset (-k)
        tidOffset _ = Nothing

        tidMod (BinOpExp (SMod Int32) x y)
          | y == primExpFromSubExp int32 d = tidOffset x
        tidMod _ = Nothing

findCandidateIndexing :: (VName -> Maybe Type)
                      -> [VName]
                      -> M.Map VName (PrimExp VName)
                      -> Stms InKernel
                      -> [Indexing]
findCandidateIndexing kernelInvariant gtids orig_vtable = concatMap (onStm orig_vtable) . stmsToList
  where onStm vtable (Let (Pattern [] [pe]) _ (BasicOp (Index arr slice)))
          | Just arr_t <- kernelInvariant arr,
            length slice == length gtids,
            Just is <- mapM onIndex $ zip3 (arrayDims arr_t) gtids slice =
              [Indexing pe arr is]
          where onIndex (d, tid, e) =
                  dimFix e >>=
                  primExpFromSubExpM (`M.lookup` vtable) >>=
                  isOffset d tid
        onStm vtable stm = execState (walkExpM (walker vtable) $ stmExp stm) mempty
        walker vtable = identityWalker { walkOnBody = modify . (<>) . onBody vtable }
        onBody vtable body =
          let vtable' = primExpTable vtable $ bodyStms body
          in concatMap (onStm vtable') $ stmsToList $ bodyStms body

replaceIndexing :: Monad m =>
                   (PatElem InKernel -> Maybe (m (VName, Slice SubExp))) -> Stms InKernel
                -> m (Stms InKernel)
replaceIndexing f = mapM onStm
  where onStm (Let (Pattern [] [pe]) aux (BasicOp Index{}))
          | Just m <- f pe = do
              (arr, slice) <- m
              return $ Let (Pattern [] [pe]) aux $ BasicOp $ Index arr slice
        onStm (Let pat aux e) = Let pat aux <$> mapExpM mapper e
        mapper = identityMapper { mapOnBody = \_ (Body aux stms res) ->
                                    Body aux <$> mapM onStm stms <*> pure res
                                }

sufficientGroups :: MonadBinder m =>
                    [(VName, SubExp, VName, SubExp)] -> SubExp
                 -> m (SubExp, SubExp)
sufficientGroups gspace group_size = do
  groups_in_dims <- forM gspace $ \(_, gd, _, ld) ->
    letSubExp "groups_in_dim" =<< eDivRoundingUp Int32 (eSubExp gd) (eSubExp ld)
  num_groups <- letSubExp "num_groups" =<<
                foldBinOp (Mul Int32) (constant (1::Int32)) groups_in_dims
  num_threads <- letSubExp "num_threads" $
                 BasicOp $ BinOp (Mul Int32) num_groups group_size
  return (num_threads, num_groups)
