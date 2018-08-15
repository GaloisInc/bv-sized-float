{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized.Float.App
Copyright   : (c) Benjamin Selfridge, 2018
                  Galois Inc.
License     : None (yet)
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

Module for handling floating-point expressions.
-}

module Data.BitVector.Sized.Float.App
  ( BVFloatApp(..)
  , RM
  , evalBVFloatAppM
  , BVFloatExpr(..)
  , getFRes
  -- * Miscellaneous functions
  -- ** 32-bit
  , f32Exp, f32Sig, f32Sgn
  , posZero32
  , negZero32
  , canonicalNaN32
  , posInfinity32
  , negInfinity32
  , isNaN32
  , isSNaN32
  , isQNaN32
  , isZero32
  , isNormal32
  , isSubnormal32
  -- ** 64-bit
  , f64Exp, f64Sig, f64Sgn
  , posZero64
  , negZero64
  , canonicalNaN64
  , posInfinity64
  , negInfinity64
  , isNaN64
  , isSNaN64
  , isQNaN64
  , isZero64
  , isNormal64
  , isSubnormal64
  -- * Smart constructors
  -- ** Integer to float
  , ui32ToF16E
  , ui32ToF32E
  , ui32ToF64E
  , i32ToF16E
  , i32ToF32E
  , i32ToF64E
  , ui64ToF16E
  , ui64ToF32E
  , ui64ToF64E
  , i64ToF16E
  , i64ToF32E
  , i64ToF64E
  -- ** Float to integer
  , f16ToUi32E
  , f16ToUi64E
  , f16ToI32E
  , f16ToI64E
  , f32ToUi32E
  , f32ToUi64E
  , f32ToI32E
  , f32ToI64E
  , f64ToUi32E
  , f64ToUi64E
  , f64ToI32E
  , f64ToI64E
  ) where

import Data.Bits
import Data.BitVector.Sized
import Data.BitVector.Sized.App
import Data.BitVector.Sized.Float
import GHC.TypeLits
import SoftFloat

-- | Type synonym for rounding-mode expression
type RM expr = expr 3

-- | Representation of a floating point operation, implicitly containing both a
-- result of the given width and the resulting exceptions.
data BVFloatApp (expr :: Nat -> *) (w :: Nat) where
  Ui32ToF16App :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 21
  Ui32ToF32App :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 37
  Ui32ToF64App :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 69
  I32ToF16App  :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 21
  I32ToF32App  :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 37
  I32ToF64App  :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 69
  Ui64ToF16App :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 21
  Ui64ToF32App :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 37
  Ui64ToF64App :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 69
  I64ToF16App  :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 21
  I64ToF32App  :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 37
  I64ToF64App  :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 69
  F16ToUi32App :: !(RM expr) -> !(expr 16) -> BVFloatApp expr 37
  F16ToUi64App :: !(RM expr) -> !(expr 16) -> BVFloatApp expr 69
  F16ToI32App  :: !(RM expr) -> !(expr 16) -> BVFloatApp expr 37
  F16ToI64App  :: !(RM expr) -> !(expr 16) -> BVFloatApp expr 69
  F32ToUi32App :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 37
  F32ToUi64App :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 69
  F32ToI32App  :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 37
  F32ToI64App  :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 69
  F64ToUi32App :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 37
  F64ToUi64App :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 69
  F64ToI32App  :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 37
  F64ToI64App  :: !(RM expr) -> !(expr 64) -> BVFloatApp expr 69

-- TODO: Fix SoftFloat's Enum instance
bvToRM :: BitVector 3 -> RoundingMode
bvToRM 0 = RoundNearEven
bvToRM 1 = RoundMinMag
bvToRM 2 = RoundMin
bvToRM 3 = RoundMax
bvToRM 4 = RoundNearMaxMag
bvToRM 6 = RoundOdd
bvToRM _ = RoundNearEven -- rather than throwing an error, we default.

efToBV :: ExceptionFlags -> BitVector 5
efToBV (ExceptionFlags ieFlag ufFlag ofFlag infFlag invFlag) =
  toBV ieFlag
  .|. (toBV ufFlag `shiftL` 1)
  .|. (toBV ofFlag `shiftL` 2)
  .|. (toBV infFlag `shiftL` 3)
  .|. (toBV invFlag `shiftL` 4)
  where toBV True = 1
        toBV False = 0

-- | Type class for expressions languages with floating point expressions.
class BVExpr expr => BVFloatExpr (expr :: Nat -> *) where
  floatAppExpr :: BVFloatApp expr w -> expr w

-- | concatenate result into a single 'BitVector'.
cr :: Result (BitVector w) -> BitVector (5 + w)
cr (Result res flags) = efToBV flags `bvConcat` res

-- | Evaluation of floating-point expressions.
evalBVFloatAppM :: Monad m
                => (forall w' . expr w' -> m (BitVector w'))
                -> BVFloatApp expr w
                -> m (BitVector w)
evalBVFloatAppM eval (Ui32ToF16App rmE xE) = cr <$> (bvUi32ToF16 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (Ui32ToF32App rmE xE) = cr <$> (bvUi32ToF32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (Ui32ToF64App rmE xE) = cr <$> (bvUi32ToF64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (I32ToF16App rmE xE) = cr <$> (bvI32ToF16 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (I32ToF32App rmE xE) = cr <$> (bvI32ToF32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (I32ToF64App rmE xE) = cr <$> (bvI32ToF64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (Ui64ToF16App rmE xE) = cr <$> (bvUi64ToF16 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (Ui64ToF32App rmE xE) = cr <$> (bvUi64ToF32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (Ui64ToF64App rmE xE) = cr <$> (bvUi64ToF64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (I64ToF16App rmE xE) = cr <$> (bvI64ToF16 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (I64ToF32App rmE xE) = cr <$> (bvI64ToF32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (I64ToF64App rmE xE) = cr <$> (bvI64ToF64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F16ToUi32App rmE xE) = cr <$> (bvF16ToUi32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F16ToUi64App rmE xE) = cr <$> (bvF16ToUi64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F16ToI32App rmE xE) = cr <$> (bvF16ToI32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F16ToI64App rmE xE) = cr <$> (bvF16ToI64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F32ToUi32App rmE xE) = cr <$> (bvF32ToUi32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F32ToUi64App rmE xE) = cr <$> (bvF32ToUi64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F32ToI32App rmE xE) = cr <$> (bvF32ToI32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F32ToI64App rmE xE) = cr <$> (bvF32ToI64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F64ToUi32App rmE xE) = cr <$> (bvF64ToUi32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F64ToUi64App rmE xE) = cr <$> (bvF64ToUi64 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F64ToI32App rmE xE) = cr <$> (bvF64ToI32 <$> (bvToRM <$> eval rmE) <*> eval xE)
evalBVFloatAppM eval (F64ToI64App rmE xE) = cr <$> (bvF64ToI64 <$> (bvToRM <$> eval rmE) <*> eval xE)

-- Integer to float
ui32ToF16E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 21
ui32ToF16E rmE e = floatAppExpr (Ui32ToF16App rmE e)

ui32ToF32E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 37
ui32ToF32E rmE e = floatAppExpr (Ui32ToF32App rmE e)

ui32ToF64E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 69
ui32ToF64E rmE e = floatAppExpr (Ui32ToF64App rmE e)

i32ToF16E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 21
i32ToF16E rmE e = floatAppExpr (I32ToF16App rmE e)

i32ToF32E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 37
i32ToF32E rmE e = floatAppExpr (I32ToF32App rmE e)

i32ToF64E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 69
i32ToF64E rmE e = floatAppExpr (I32ToF64App rmE e)

ui64ToF16E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 21
ui64ToF16E rmE e = floatAppExpr (Ui64ToF16App rmE e)

ui64ToF32E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 37
ui64ToF32E rmE e = floatAppExpr (Ui64ToF32App rmE e)

ui64ToF64E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 69
ui64ToF64E rmE e = floatAppExpr (Ui64ToF64App rmE e)

i64ToF16E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 21
i64ToF16E rmE e = floatAppExpr (I64ToF16App rmE e)

i64ToF32E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 37
i64ToF32E rmE e = floatAppExpr (I64ToF32App rmE e)

i64ToF64E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 69
i64ToF64E rmE e = floatAppExpr (I64ToF64App rmE e)

-- Float to integer
f16ToUi32E :: BVFloatExpr expr => RM expr -> expr 16 -> expr 37
f16ToUi32E rmE e = floatAppExpr (F16ToUi32App rmE e)

f16ToUi64E :: BVFloatExpr expr => RM expr -> expr 16 -> expr 69
f16ToUi64E rmE e = floatAppExpr (F16ToUi64App rmE e)

f16ToI32E  :: BVFloatExpr expr => RM expr -> expr 16 -> expr 37
f16ToI32E rmE e = floatAppExpr (F16ToI32App rmE e)

f16ToI64E  :: BVFloatExpr expr => RM expr -> expr 16 -> expr 69
f16ToI64E rmE e = floatAppExpr (F16ToI64App rmE e)

f32ToUi32E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 37
f32ToUi32E rmE e = floatAppExpr (F32ToUi32App rmE e)

f32ToUi64E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 69
f32ToUi64E rmE e = floatAppExpr (F32ToUi64App rmE e)

f32ToI32E  :: BVFloatExpr expr => RM expr -> expr 32 -> expr 37
f32ToI32E rmE e = floatAppExpr (F32ToI32App rmE e)

f32ToI64E  :: BVFloatExpr expr => RM expr -> expr 32 -> expr 69
f32ToI64E rmE e = floatAppExpr (F32ToI64App rmE e)

f64ToUi32E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 37
f64ToUi32E rmE e = floatAppExpr (F64ToUi32App rmE e)

f64ToUi64E :: BVFloatExpr expr => RM expr -> expr 64 -> expr 69
f64ToUi64E rmE e = floatAppExpr (F64ToUi64App rmE e)

f64ToI32E  :: BVFloatExpr expr => RM expr -> expr 64 -> expr 37
f64ToI32E rmE e = floatAppExpr (F64ToI32App rmE e)

f64ToI64E  :: BVFloatExpr expr => RM expr -> expr 64 -> expr 69
f64ToI64E rmE e = floatAppExpr (F64ToI64App rmE e)

-- Miscellaneous

-- 32
f32Exp :: BVExpr expr => expr 32 -> expr 8
f32Exp e = extractE 23 e

f32Sig :: BVExpr expr => expr 32 -> expr 23
f32Sig e = extractE 0 e

f32Sgn :: BVExpr expr => expr 32 -> expr 1
f32Sgn e = extractE 31 e

isNaN32 :: BVExpr expr => expr 32 -> expr 1
isNaN32 e = (f32Exp e `eqE` litBV 0xFF) `andE` (notE (f32Sig e `eqE` litBV 0))

isSNaN32 :: BVExpr expr => expr 32 -> expr 1
isSNaN32 e = isNaN32 e `andE` notE (extractE 22 e)

isQNaN32 :: BVExpr expr => expr 32 -> expr 1
isQNaN32 e = isNaN32 e `andE` extractE 22 e

isSubnormal32 :: BVExpr expr => expr 32 -> expr 1
isSubnormal32 e = (f32Exp e `eqE` litBV 0x0) `andE` (notE (isZero32 e))

isNormal32 :: BVExpr expr => expr 32 -> expr 1
isNormal32 e = (litBV 0x0 `ltuE` f32Exp e) `andE` (f32Exp e `ltuE` litBV 0xff)

canonicalNaN32 :: BVExpr expr => expr 32
canonicalNaN32 = litBV 0x7FC00000

posZero32 :: BVExpr expr => expr 32
posZero32 = litBV 0x00000000

negZero32 :: BVExpr expr => expr 32
negZero32 = litBV 0x80000000

isZero32 :: BVExpr expr => expr 32 -> expr 1
isZero32 e = (e `eqE` posZero32) `orE` (e `eqE` negZero32)

posInfinity32 :: BVExpr expr => expr 32
posInfinity32 = litBV 0x7F800000

negInfinity32 :: BVExpr expr => expr 32
negInfinity32 = litBV 0xFF800000

-- 64
f64Exp :: BVExpr expr => expr 64 -> expr 11
f64Exp e = extractE 52 e

f64Sig :: BVExpr expr => expr 64 -> expr 52
f64Sig e = extractE 0 e

f64Sgn :: BVExpr expr => expr 64 -> expr 1
f64Sgn e = extractE 63 e

isNaN64 :: BVExpr expr => expr 64 -> expr 1
isNaN64 e = (f64Exp e `eqE` litBV 0x7FF) `andE` (notE (f64Sig e `eqE` litBV 0))

isSNaN64 :: BVExpr expr => expr 64 -> expr 1
isSNaN64 e = isNaN64 e `andE` notE (extractE 51 e)

isQNaN64 :: BVExpr expr => expr 64 -> expr 1
isQNaN64 e = isNaN64 e `andE` extractE 51 e

isSubnormal64 :: BVExpr expr => expr 64 -> expr 1
isSubnormal64 e = (f64Exp e `eqE` litBV 0x0) `andE` (notE (isZero64 e))

isNormal64 :: BVExpr expr => expr 64 -> expr 1
isNormal64 e = (litBV 0x0 `ltuE` f64Exp e) `andE` (f64Exp e `ltuE` litBV 0xff)

canonicalNaN64 :: BVExpr expr => expr 64
canonicalNaN64 = litBV 0x7FF8000000000000

posZero64 :: BVExpr expr => expr 64
posZero64 = litBV 0x0000000000000000

negZero64 :: BVExpr expr => expr 64
negZero64 = litBV 0x8000000000000000

isZero64 :: BVExpr expr => expr 64 -> expr 1
isZero64 e = (e `eqE` posZero64) `orE` (e `eqE` negZero64)

posInfinity64 :: BVExpr expr => expr 64
posInfinity64 = litBV 0x7FF0000000000000

negInfinity64 :: BVExpr expr => expr 64
negInfinity64 = litBV 0xFFF0000000000000

getFRes :: (KnownNat w, BVExpr expr) => expr (5 + w) -> (expr w, expr 5)
getFRes e = (extractE 0 e, extractE 32 e)
