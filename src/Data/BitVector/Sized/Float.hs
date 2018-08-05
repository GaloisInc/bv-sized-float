{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized.Float
Copyright   : (c) Benjamin Selfridge, 2018
                  Galois Inc.
License     : BSD3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

Floating point operations for bv-sized.
-}

module Data.BitVector.Sized.Float where

import Data.BitVector.Sized
import Data.Parameterized
import Data.Word
import GHC.TypeLits
import SoftFloat

data FloatType = Float16
               | Float32
               | Float64

type Float16 = 'Float16
type Float32 = 'Float32
type Float64 = 'Float64

data FloatTypeRepr :: FloatType -> * where
  Float16Repr :: FloatTypeRepr Float16
  Float32Repr :: FloatTypeRepr Float32
  Float64Repr :: FloatTypeRepr Float64

instance KnownRepr FloatTypeRepr Float16 where knownRepr = Float16Repr
instance KnownRepr FloatTypeRepr Float32 where knownRepr = Float32Repr
instance KnownRepr FloatTypeRepr Float64 where knownRepr = Float64Repr

type family FloatWidth (ft :: FloatType) :: Nat where
  FloatWidth Float16 = 16
  FloatWidth Float32 = 32
  FloatWidth Float64 = 64

type family FloatWord (ft :: FloatType) :: * where
  FloatWord Float16 = Word16
  FloatWord Float32 = Word32
  FloatWord Float64 = Word64

data FloatBV (ft :: FloatType) where
  FloatBV :: FloatTypeRepr ft -> BitVector (FloatWidth ft) -> FloatBV ft

bvBinaryOpFloat :: (RoundingMode -> Word16 -> Word16 -> Result Word16)
                -> (RoundingMode -> Word32 -> Word32 -> Result Word32)
                -> (RoundingMode -> Word64 -> Word64 -> Result Word64)
                -> RoundingMode -> FloatBV ft -> FloatBV ft -> Result (FloatBV ft)
bvBinaryOpFloat flop16 flop32 flop64 rm (FloatBV fRepr (BV wRepr x)) (FloatBV _ (BV _ y)) =
  case fRepr of
    Float16Repr ->
      let Result wordVal flags = flop16 rm (fromIntegral x) (fromIntegral y)
      in Result (FloatBV Float16Repr (BV wRepr (fromIntegral wordVal))) flags
    Float32Repr ->
      let Result wordVal flags = flop32 rm (fromIntegral x) (fromIntegral y)
      in Result (FloatBV Float32Repr (BV wRepr (fromIntegral wordVal))) flags
    Float64Repr ->
      let Result wordVal flags = flop64 rm (fromIntegral x) (fromIntegral y)
      in Result (FloatBV Float64Repr (BV wRepr (fromIntegral wordVal))) flags

-- bvBinaryOpFloat flop (FloatBV Float16Repr (BV wRepr x)) (FloatBV _ (BV _ y)) =
--   let Result wordVal flags = flop (fromIntegral x) (fromIntegral y)
--   in Result (FloatBV Float16Repr (BV wRepr (fromIntegral wordVal))) flags
-- bvBinaryOpFloat flop (FloatBV Float32Repr (BV wRepr x)) (FloatBV _ (BV _ y)) =
--   let Result wordVal flags = flop (fromIntegral x) (fromIntegral y)
--   in Result (FloatBV Float32Repr (BV wRepr (fromIntegral wordVal))) flags
-- bvBinaryOpFloat flop (FloatBV Float64Repr (BV wRepr x)) (FloatBV _ (BV _ y)) =
--   let Result wordVal flags = flop (fromIntegral x) (fromIntegral y)
--   in Result (FloatBV Float64Repr (BV wRepr (fromIntegral wordVal))) flags

bvAddF :: RoundingMode -> FloatBV ft -> FloatBV ft -> Result (FloatBV ft)
bvAddF = bvBinaryOpFloat f16Add f32Add f64Add

-- instance Show (FloatBitVector ft) where
--   show (FloatBitVector bv) = show bv

-- instance ShowF FloatBitVector

