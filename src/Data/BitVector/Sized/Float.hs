{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
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
import GHC.TypeLits
-- import SoftFloat

data FloatType = Float16
               | Float32
               | Float64

type Float16 = 'Float16
type Float32 = 'Float32
type Float64 = 'Float64

type family FloatWidth (fw :: FloatType) :: Nat where
  FloatWidth Float16 = 16
  FloatWidth Float32 = 32
  FloatWidth Float64 = 64

data FloatBitVector (ft :: FloatType) where
  FloatBitVector :: BitVector (FloatWidth ft) -> FloatBitVector ft

instance Show (FloatBitVector ft) where
  show (FloatBitVector bv) = show bv

instance ShowF FloatBitVector
