{-# LANGUAGE FlexibleContexts #-}
-- | Perform copy propagation.  This is done by invoking the
-- simplifier with no rules, so hoisting and dead-code elimination may
-- also take place.
module Futhark.Transform.CopyPropagate
       (copyPropagateInBindings)
       where

import Futhark.MonadFreshNames
import Futhark.Representation.AST
import Futhark.Optimise.Simplifier.Simplify
import Futhark.Optimise.Simplifier.Lore
import Futhark.Optimise.Simplifier.Engine (MonadEngine)

copyPropagateInBindings :: (MonadFreshNames m,
                            HasTypeEnv m,
                            MonadEngine (SimpleM lore)) =>
                           SimpleOps (SimpleM lore)
                        -> [Binding lore]
                        -> m [Binding lore]
copyPropagateInBindings simpl =
  fmap (map removeBindingWisdom) .
  simplifyBindings simpl ([], []) Nothing
