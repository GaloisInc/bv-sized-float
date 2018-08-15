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
  , isNaN32
  , isNaN64
  , canonicalNaN32
  , canonicalNaN64
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

-- Miscellaneous

f32Exp :: BVExpr expr => expr 32 -> expr 8
f32Exp e = extractE 23 e

f32Sig :: BVExpr expr => expr 32 -> expr 23
f32Sig e = extractE 0 e

f64Exp :: BVExpr expr => expr 64 -> expr 11
f64Exp e = extractE 52 e

f64Sig :: BVExpr expr => expr 64 -> expr 52
f64Sig e = extractE 0 e

isNaN32 :: BVExpr expr => expr 32 -> expr 1
isNaN32 e = (f32Exp e `eqE` litBV 0xFF) `andE` (notE (f32Sig e `eqE` litBV 0))

canonicalNaN32 :: BVExpr expr => expr 32
canonicalNaN32 = litBV 0x7FC00000

isNaN64 :: BVExpr expr => expr 64 -> expr 1
isNaN64 e = (f64Exp e `eqE` litBV 0x7FF) `andE` (notE (f64Sig e `eqE` litBV 0))

canonicalNaN64 :: BVExpr expr => expr 64
canonicalNaN64 = litBV 0x7FF8000000000000

getFRes :: (KnownNat w, BVExpr expr) => expr (5 + w) -> (expr w, expr 5)
getFRes e = (extractE 0 e, extractE 32 e)
