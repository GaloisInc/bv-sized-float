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
  , BVFloatExpr(..)
  , getFRes
  -- -- * Smart constructors
  , ui32ToF32E
  -- -- * Integer to float conversions
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
  Ui32ToF32App :: !(RM expr) -> !(expr 32) -> BVFloatApp expr 37

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

-- | concatenate result into a single 'BitVector'.
cr :: Result (BitVector w) -> BitVector (5 + w)
cr (Result res flags) = efToBV flags `bvConcat` res

-- | Evaluation of floating-point expressions.
evalBVFloatAppM :: Monad m
                => (forall w' . expr w' -> m (BitVector w'))
                -> BVFloatApp expr w
                -> m (BitVector w)
evalBVFloatAppM eval (Ui32ToF32App rmE xE) = cr <$> (bvUi32ToF32 <$> (bvToRM <$> eval rmE) <*> eval xE)

class BVExpr expr =>  BVFloatExpr (expr :: Nat -> *) where
  floatAppExpr :: BVFloatApp expr w -> expr w

ui32ToF32E :: BVFloatExpr expr => RM expr -> expr 32 -> expr 37
ui32ToF32E rmE e = floatAppExpr (Ui32ToF32App rmE e)

getFRes :: (KnownNat w, BVFloatExpr expr) => expr (5 + w) -> (expr w, expr 5)
getFRes e = (extractE 0 e, extractE 32 e)
