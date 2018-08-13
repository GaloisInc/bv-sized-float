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
  -- , evalBVFloatApp
  , evalBVFloatAppM
  -- -- * Smart constructors
  -- , BVFloatExpr(..)
  -- -- * Integer to float conversions
  ) where

-- import Data.Parameterized
-- import Data.Parameterized.TH.GADT
import Data.Bits
import Data.BitVector.Sized
import Data.BitVector.Sized.Float
import GHC.TypeLits
import SoftFloat

-- extern THREAD_LOCAL uint_fast8_t softfloat_roundingMode;
-- enum {
--     softfloat_round_near_even   = 0,
--     softfloat_round_minMag      = 1,
--     softfloat_round_min         = 2,
--     softfloat_round_max         = 3,
--     softfloat_round_near_maxMag = 4,
--     softfloat_round_odd         = 6
-- };

-- extern THREAD_LOCAL uint_fast8_t softfloat_exceptionFlags;
-- enum {
--     softfloat_flag_inexact   =  1,
--     softfloat_flag_underflow =  2,
--     softfloat_flag_overflow  =  4,
--     softfloat_flag_infinite  =  8,
--     softfloat_flag_invalid   = 16
-- };

-- | Type synonym for rounding-mode expression
type RM expr = expr 3

-- | Representation of a floating point operation, implicitly containing both a
-- result of the given width and the resulting exceptions.
data BVFloatApp (expr :: Nat -> *) (w :: Nat) where
  Ui32ToF32App :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 37

-- -- | Evaluation of a floating point operation; we can get either the result or the
-- -- exceptions.
-- data BVFloatApp (expr :: Nat -> *) (w :: Nat) where
--   FloatResApp :: BVFloatOp expr w -> BVFloatApp expr w
--   ExceptionsApp :: BVFloatOp expr w -> BVFloatApp expr 5

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

cr :: Result (BitVector w) -> BitVector (5 + w)
cr (Result res flags) = efToBV flags `bvConcat` res

-- | Evaluation of floating-point expressions.
evalBVFloatAppM :: Monad m
                => (forall w' . expr w' -> m (BitVector w'))
                -> BVFloatApp expr w
                -> m (BitVector w)
evalBVFloatAppM eval (Ui32ToF32App rmE xE) = cr <$> (bvUi32ToF32 <$> (bvToRM <$> eval rmE) <*> eval xE)
