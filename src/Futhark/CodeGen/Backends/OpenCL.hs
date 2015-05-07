{-# LANGUAGE QuasiQuotes, FlexibleContexts #-}
module Futhark.CodeGen.Backends.OpenCL
  ( compileProg
  ) where

import Control.Monad
import Control.Monad.Writer
import Data.Traversable hiding (forM)
import Data.Loc (noLoc)
import qualified Data.HashSet as HS

import Prelude

import qualified Language.C.Syntax as C
import qualified Language.C.Quote.OpenCL as C

import Futhark.Representation.ExplicitMemory (Prog, pretty)
import qualified Futhark.CodeGen.Backends.GenericC as GenericC
import Futhark.CodeGen.Backends.SimpleRepresentation
import Futhark.CodeGen.KernelImp
import qualified Futhark.CodeGen.KernelImpGen as KernelImpGen
import Futhark.MonadFreshNames

compileProg :: Prog -> Either String String
compileProg prog = do
  prog' <- KernelImpGen.compileProg prog
  let header = unlines [ "#include <CL/cl.h>\n" ]
  kernels <- forM (getKernels prog') $ \kernel -> do
    kernel' <- compileKernel kernel
    return (kernelName kernel, [C.cinit|$string:(openClKernelHeader kernel ++
                                                 "\n" ++
                                                 pretty kernel')|])
  return $
    header ++
    GenericC.compileProg callKernels pointerQuals (openClDecls kernels) openClInit prog'

callKernels :: GenericC.OpCompiler Kernel
callKernels kernel = do
  zipWithM_ mkBuffer [(0::Int)..] $ kernelCopyIn kernel
  devReads <-
    zipWithM mkBuffer [length (kernelCopyIn kernel)..] $ kernelCopyOut kernel
  global_work_size <- newVName "global_work_size"
  let kernel_size = GenericC.dimSizeToExp $ kernelSize kernel

  GenericC.stm [C.cstm|{
    size_t $id:global_work_size = $exp:kernel_size;
    assert(clEnqueueNDRangeKernel(fut_cl_queue, $id:kernel_name, 1, NULL,
                                  &$id:global_work_size, NULL,
                                  0, NULL, NULL)
           == CL_SUCCESS);
    }|]

  sequence_ devReads
  GenericC.stm [C.cstm|assert(clFinish(fut_cl_queue) == CL_SUCCESS);|]
  return GenericC.Done

  where mkBuffer i (CopyMemory hostbuf size copy_before) = do
          let size' = GenericC.dimSizeToExp size
          devbuf <- newVName $ baseString hostbuf ++ "_dev"
          errorname <- newVName "error"
          GenericC.decl [C.cdecl|typename cl_mem $id:devbuf;|]
          GenericC.stm [C.cstm|{
            typename cl_int $id:errorname;
            $id:devbuf = clCreateBuffer(fut_cl_context, CL_MEM_READ_WRITE, $exp:size', NULL, &$id:errorname);
            assert($id:errorname == 0);
            assert(clSetKernelArg($id:kernel_name, $int:i, sizeof($id:devbuf), &$id:devbuf)
                   == CL_SUCCESS);
            }|]
          when copy_before $
            readOrWriteBuffer "clEnqueueWriteBuffer" hostbuf devbuf size'
          return $ readOrWriteBuffer "clEnqueueReadBuffer" hostbuf devbuf size'

        mkBuffer i (CopyScalar hostvar _) = do
          GenericC.stm [C.cstm|{
            assert(clSetKernelArg($id:kernel_name, $int:i, sizeof($id:hostvar), &$id:hostvar)
                   == CL_SUCCESS);
            }|]
          return $ return ()

        readOrWriteBuffer readwrite hostbuf devbuf size =
          GenericC.stm [C.cstm|{
            assert($id:readwrite(fut_cl_queue, $id:devbuf,
                                 CL_FALSE, 0, $exp:size, $id:hostbuf,
                                 0, NULL, NULL)
                    == CL_SUCCESS);
            }|]

        kernel_name = kernelName kernel

failOnKernels :: GenericC.OpCompiler Kernel
failOnKernels kernel =
  fail $ "Asked to call kernel " ++ kernelName kernel ++ " while already inside a kernel"

pointerQuals ::  GenericC.PointerQuals Kernel
pointerQuals "global"    = return [C.TCLglobal noLoc]
pointerQuals "local"     = return [C.TCLlocal noLoc]
pointerQuals "private"   = return [C.TCLprivate noLoc]
pointerQuals "constant"  = return [C.TCLconstant noLoc]
pointerQuals "writeonly" = return [C.TCLwriteonly noLoc]
pointerQuals "readonly"  = return [C.TCLreadonly noLoc]
pointerQuals "kernel"    = return [C.TCLkernel noLoc]
pointerQuals s           = fail $ "'" ++ s ++ "' is not an OpenCL address space."

compileKernel :: Kernel -> Either String C.Func
compileKernel kernel =
  let (funbody,_) = GenericC.runCompilerM (Program []) failOnKernels pointerQuals blankNameSource $
                    GenericC.collect $ GenericC.compileCode $ kernelBody kernel

      asParam (CopyScalar name bt) =
        let ctp = GenericC.scalarTypeToCType bt
        in [C.cparam|$ty:ctp $id:name|]
      asParam (CopyMemory name _ _) =
        [C.cparam|__global unsigned char *$id:name|]

      inparams = map asParam $ kernelCopyIn kernel
      outparams = map asParam $ kernelCopyOut kernel
  in Right [C.cfun|__kernel void $id:(kernelName kernel) ($params:(inparams++outparams)) {
               const uint $id:(kernelThreadNum kernel) = get_global_id(0);
               $items:funbody
}|]

openClDecls :: [(String, C.Initializer)] -> [C.Definition]
openClDecls kernels =
  clGlobals ++ kernelSourceDeclarations ++ kernelDeclarations ++ [buildKernelFunction, setupFunction]
  where clGlobals =
          [ [C.cedecl|typename cl_context fut_cl_context;|]
          , [C.cedecl|typename cl_command_queue fut_cl_queue;|]
          ]

        kernelSourceDeclarations =
          [ [C.cedecl|const char $id:(name++"_src")[] = $init:kernel;|]
          | (name, kernel) <- kernels ]

        kernelDeclarations =
          [ [C.cedecl|typename cl_kernel $id:name;|]
          | (name, _) <- kernels ]

        setupFunction = [C.cedecl|
void setup_opencl() {
  typename cl_int error;
  typename cl_platform_id platform;
  typename cl_device_id device;
  typename cl_uint platforms, devices;
  // Fetch the Platform and Device IDs; we only want one.
  error = clGetPlatformIDs(1, &platform, &platforms);
  assert(error == 0);
  assert(platforms > 0);
  error = clGetDeviceIDs(platform, CL_DEVICE_TYPE_ALL, 1, &device, &devices);
  assert(error == 0);
  assert(devices > 0);
  typename cl_context_properties properties[] = {
    CL_CONTEXT_PLATFORM,
    (typename cl_context_properties)platform,
    0
  };
  // Note that nVidia's OpenCL requires the platform property
  fut_cl_context = clCreateContext(properties, 1, &device, NULL, NULL, &error);
  fut_cl_queue = clCreateCommandQueue(fut_cl_context, device, 0, &error);
  // Load all the kernels.
  $stms:(map (loadKernelByName . fst) kernels)
}
    |]

        buildKernelFunction = [C.cedecl|
typename cl_build_status build_opencl_kernel(typename cl_program program, typename cl_device_id device, const char* options) {
  typename cl_int ret_val = clBuildProgram(program, 1, &device, options, NULL, NULL);

  // Avoid termination due to CL_BUILD_PROGRAM_FAILURE
  if (ret_val != CL_SUCCESS && ret_val != CL_BUILD_PROGRAM_FAILURE) {
    assert(ret_val == 0);
  }

  typename cl_build_status build_status;
  ret_val = clGetProgramBuildInfo(program,
                                  device,
                                  CL_PROGRAM_BUILD_STATUS,
                                  sizeof(cl_build_status),
                                  &build_status,
                                  NULL);
  assert(ret_val == 0);

  if (build_status != CL_SUCCESS) {
    char *build_log;
    size_t ret_val_size;
    ret_val = clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG, 0, NULL, &ret_val_size);
    assert(ret_val == 0);

    build_log = malloc(ret_val_size+1);
    clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG, ret_val_size, build_log, NULL);
    assert(ret_val == 0);

    // The spec technically does not say whether the build log is zero-terminated, so let's be careful.
    build_log[ret_val_size] = '\0';

    fprintf(stderr, "Build log:\n%s", build_log);

    free(build_log);
  }

  return build_status;
}
|]

loadKernelByName :: String -> C.Stm
loadKernelByName name = [C.cstm|{
  size_t src_size;
  typename cl_program prog;
  fprintf(stderr, "look at me, loading this kernel:\n%s\n", $id:srcname);
  error = 0;
  src_size = sizeof($id:srcname);
  const char* src_ptr[] = {$id:srcname};
  prog = clCreateProgramWithSource(fut_cl_context, 1, src_ptr, &src_size, &error);
  assert(error == 0);
  assert(build_opencl_kernel(prog, device, "") == CL_SUCCESS);
  $id:name = clCreateKernel(prog, $string:name, &error);
  assert(error == 0);
  fprintf(stderr, "I guess it worked.\n");
  }|]
  where srcname = name ++ "_src"

openClInit :: [C.Stm]
openClInit =
  [[C.cstm|setup_opencl();|]]

kernelId :: Kernel -> Int
kernelId = baseTag . kernelThreadNum

kernelName :: Kernel -> String
kernelName = ("kernel_"++) . show . kernelId

getKernels :: Program -> [Kernel]
getKernels = execWriter . traverse getFunKernels
  where getFunKernels kernel =
          tell [kernel] >> return kernel

openClKernelHeader :: Kernel -> String
openClKernelHeader kernel =
  unlines $
  pragmas ++ map pretty (utilityFunctions ++ funs32_used ++ funs64_used)
  where kernel_funs = functionsCalled $ kernelBody kernel
        used_in_kernel = (`HS.member` kernel_funs) . nameFromString . fst
        funs32_used = map snd $ filter used_in_kernel funs32
        funs64_used = map snd $ filter used_in_kernel funs64
        pragmas = if null funs64_used
                  then []
                  else ["#pragma OPENCL EXTENSION cl_khr_fp64 : enable"]

        funs32 = [("toFloat32", c_toFloat32),
                  ("trunc32", c_trunc32),
                  ("log32", c_log32),
                  ("sqrt32", c_sqrt32),
                  ("exp32", c_exp32)]

        funs64 = [("toFloat64", c_toFloat64),
                  ("trunc64", c_trunc64),
                  ("log64", c_log64),
                  ("sqrt64", c_sqrt64),
                  ("exp64", c_exp64)]

utilityFunctions :: [C.Func]
utilityFunctions = [
  [C.cfun|
  // From musl.
  __global void *memcpy(__global void *restrict dest, __global const void *restrict src, size_t n)
  {
    __global unsigned char *d = dest;
    __global const unsigned char *s = src;
    // These were #defines in the musl source code.
    size_t SS = sizeof(size_t), ALIGN = sizeof(size_t)-1, ONES=((size_t)-1/UCHAR_MAX);
    if (((typename uintptr_t)d & ALIGN) != ((typename uintptr_t)s & ALIGN)) {
      goto misaligned;
    }
    for (; ((typename uintptr_t)d & ALIGN) && n; n--) {
      *d++ = *s++;
    }
    if (n) {
      __global size_t *wd = (__global void *)d;
      __global const size_t *ws = (__global const void *)s;
      for (; n>=SS; n-=SS) *wd++ = *ws++;
      d = (__global void *)wd;
      s = (__global const void *)ws;

      misaligned:
      for (; n; n--) {
        *d++ = *s++;
      }
    }
    return dest;
  }
   |],

  [C.cfun|
  // From musl.
  __global void *memmove(__global void *dest, __global const void *src, size_t n)
  {
    __global char *d = dest;
    __global const char *s = src;
    size_t WS = sizeof(size_t);
    if (d==s) { return d; }
    if (s+n <= d || d+n <= s) { return memcpy(d, s, n); }
    if (d<s) {
      if ((typename uintptr_t)s % WS == (typename uintptr_t)d % WS) {
        while ((typename uintptr_t)d % WS) {
        if (!n--) { return dest; }
          *d++ = *s++;
        }
        for (; n>=WS; n-=WS, d+=WS, s+=WS) {
          *(__global size_t *)d = *(__global size_t *)s;
        }
      }
      for (; n; n--) { *d++ = *s++; }
    } else {
      if ((typename uintptr_t)s % WS == (typename uintptr_t)d % WS) {
        while ((typename uintptr_t)(d+n) % WS) {
          if (!n--) { return dest; }
          d[n] = s[n];
        }
        while (n>=WS) {
          n-=WS;
          *(__global size_t *)(d+n) = *(__global size_t *)(s+n);
        }
      }
      while (n) { n--, d[n] = s[n]; }
    }
    return dest;
  }
   |]
                   ]
