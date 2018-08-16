{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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

module Data.BitVector.Sized.Float
  ( -- * Integer to floating point conversions
    bvUi32ToF16
  , bvUi32ToF32
  , bvUi32ToF64
  , bvI32ToF16
  , bvI32ToF32
  , bvI32ToF64
  , bvUi64ToF16
  , bvUi64ToF32
  , bvUi64ToF64
  , bvI64ToF16
  , bvI64ToF32
  , bvI64ToF64

    -- * Floating point to integer conversions
  , bvF16ToUi32
  , bvF16ToUi64
  , bvF16ToI32
  , bvF16ToI64
  , bvF32ToUi32
  , bvF32ToUi64
  , bvF32ToI32
  , bvF32ToI64
  , bvF64ToUi32
  , bvF64ToUi64
  , bvF64ToI32
  , bvF64ToI64

    -- * Floating point to floating point conversions
  , bvF16ToF32
  , bvF16ToF64
  , bvF32ToF16
  , bvF32ToF64
  , bvF64ToF16
  , bvF64ToF32


    -- * 16-bit operations
  , bvF16RoundToInt
  , bvF16Add
  , bvF16Sub
  , bvF16Mul
  , bvF16MulAdd
  , bvF16Div
  , bvF16Rem
  , bvF16Sqrt
  , bvF16Eq
  , bvF16Le
  , bvF16Lt
  , bvF16EqSignaling
  , bvF16LeQuiet
  , bvF16LtQuiet
  , bvF16IsSignalingNaN

    -- * 32-bit operations
  , bvF32RoundToInt
  , bvF32Add
  , bvF32Sub
  , bvF32Mul
  , bvF32MulAdd
  , bvF32Div
  , bvF32Rem
  , bvF32Sqrt
  , bvF32Eq
  , bvF32Le
  , bvF32Lt
  , bvF32EqSignaling
  , bvF32LeQuiet
  , bvF32LtQuiet
  , bvF32IsSignalingNaN

    -- * 64-bit operations
  , bvF64RoundToInt
  , bvF64Add
  , bvF64Sub
  , bvF64Mul
  , bvF64MulAdd
  , bvF64Div
  , bvF64Rem
  , bvF64Sqrt
  , bvF64Eq
  , bvF64Le
  , bvF64Lt
  , bvF64EqSignaling
  , bvF64LeQuiet
  , bvF64LtQuiet
  , bvF64IsSignalingNaN
  ) where

import Data.BitVector.Sized
import Data.Int
import Data.Word
import Foreign.C.Types
import GHC.TypeLits
import SoftFloat

type family WordType (n :: Nat) :: * where
  WordType 16 = Word16
  WordType 32 = Word32
  WordType 64 = Word64

type family IntType (n :: Nat) :: * where
  IntType 16 = Int16
  IntType 32 = Int32
  IntType 64 = Int64

liftF1U :: (KnownNat w, Integral (WordType w),
            KnownNat w', Integral (WordType w'))
        => (RoundingMode -> WordType w -> Result (WordType w'))
        -> RoundingMode -> BitVector w -> Result (BitVector w')
liftF1U flop1 rm bv =
  let Result f fFlags = flop1 rm (fromIntegral $ bvIntegerU bv)
  in  Result (fromIntegral f) fFlags

liftF1SU :: (KnownNat w, Integral (IntType w),
            KnownNat w', Integral (WordType w'))
        => (RoundingMode -> IntType w -> Result (WordType w'))
        -> RoundingMode -> BitVector w -> Result (BitVector w')
liftF1SU flop1 rm bv =
  let Result f fFlags = flop1 rm (fromIntegral $ bvIntegerS bv)
  in  Result (fromIntegral f) fFlags

liftF1US :: (KnownNat w, Integral (WordType w),
            KnownNat w', Integral (IntType w'))
        => (RoundingMode -> WordType w -> Result (IntType w'))
        -> RoundingMode -> BitVector w -> Result (BitVector w')
liftF1US flop1 rm bv =
  let Result f fFlags = flop1 rm (fromIntegral $ bvIntegerU bv)
  in  Result (fromIntegral f) fFlags

liftF1Bool :: (KnownNat w, Integral (WordType w))
           => (RoundingMode -> WordType w -> Result CBool)
           -> RoundingMode -> BitVector w -> Result Bool
liftF1Bool flop1 rm bv =
  let Result wBool fFlags = flop1 rm (fromIntegral $ bvIntegerU bv)
  in  Result (wBool /= 0) fFlags

liftF2 :: (KnownNat w, Integral (WordType w))
       => (RoundingMode -> WordType w -> WordType w -> Result (WordType w))
       -> RoundingMode -> BitVector w -> BitVector w -> Result (BitVector w)
liftF2 flop2 rm bv1 bv2 =
  let Result f fFlags = flop2 rm (fromIntegral $ bvIntegerU bv1) (fromIntegral $ bvIntegerU bv2)
  in  Result (fromIntegral f) fFlags

liftF2Bool :: (KnownNat w, Integral (WordType w))
           => (RoundingMode -> WordType w -> WordType w -> Result CBool)
           -> RoundingMode -> BitVector w -> BitVector w -> Result Bool
liftF2Bool flop2 rm bv1 bv2 =
  let Result wBool fFlags = flop2 rm (fromIntegral $ bvIntegerU bv1) (fromIntegral $ bvIntegerU bv2)
  in  Result (wBool /= 0) fFlags

liftF3 :: (KnownNat w, Integral (WordType w))
       => (RoundingMode -> WordType w -> WordType w -> WordType w -> Result (WordType w))
       -> RoundingMode -> BitVector w -> BitVector w -> BitVector w -> Result (BitVector w)
liftF3 flop3 rm bv1 bv2 bv3 =
  let Result f fFlags = flop3 rm (fromIntegral $ bvIntegerU bv1) (fromIntegral $ bvIntegerU bv2) (fromIntegral $ bvIntegerU bv3)
  in  Result (fromIntegral f) fFlags

-- Integer to floating point

bvUi32ToF16 :: RoundingMode -> BitVector 32 -> Result (BitVector 16)
bvUi32ToF16 = liftF1U ui32ToF16

bvUi32ToF32 :: RoundingMode -> BitVector 32 -> Result (BitVector 32)
bvUi32ToF32 = liftF1U ui32ToF32

bvUi32ToF64 :: RoundingMode -> BitVector 32 -> Result (BitVector 64)
bvUi32ToF64 = liftF1U ui32ToF64

bvI32ToF16 :: RoundingMode -> BitVector 32 -> Result (BitVector 16)
bvI32ToF16 = liftF1SU i32ToF16

bvI32ToF32 :: RoundingMode -> BitVector 32 -> Result (BitVector 32)
bvI32ToF32 = liftF1SU i32ToF32

bvI32ToF64 :: RoundingMode -> BitVector 32 -> Result (BitVector 64)
bvI32ToF64 = liftF1SU i32ToF64

bvUi64ToF16 :: RoundingMode -> BitVector 64 -> Result (BitVector 16)
bvUi64ToF16 = liftF1U ui64ToF16

bvUi64ToF32 :: RoundingMode -> BitVector 64 -> Result (BitVector 32)
bvUi64ToF32 = liftF1U ui64ToF32

bvUi64ToF64 :: RoundingMode -> BitVector 64 -> Result (BitVector 64)
bvUi64ToF64 = liftF1U ui64ToF64

bvI64ToF16 :: RoundingMode -> BitVector 64 -> Result (BitVector 16)
bvI64ToF16 = liftF1SU i64ToF16

bvI64ToF32 :: RoundingMode -> BitVector 64 -> Result (BitVector 32)
bvI64ToF32 = liftF1SU i64ToF32

bvI64ToF64 :: RoundingMode -> BitVector 64 -> Result (BitVector 64)
bvI64ToF64 = liftF1SU i64ToF64

-- Floating point to integer

bvF16ToUi32 :: RoundingMode -> BitVector 16 -> Result (BitVector 32)
bvF16ToUi32 = liftF1U f16ToUi32

bvF16ToUi64 :: RoundingMode -> BitVector 16 -> Result (BitVector 64)
bvF16ToUi64 = liftF1U f16ToUi64

bvF16ToI32 :: RoundingMode -> BitVector 16 -> Result (BitVector 32)
bvF16ToI32  = liftF1US f16ToI32

bvF16ToI64 :: RoundingMode -> BitVector 16 -> Result (BitVector 64)
bvF16ToI64  = liftF1US f16ToI64

bvF32ToUi32 :: RoundingMode -> BitVector 32 -> Result (BitVector 32)
bvF32ToUi32 = liftF1U f32ToUi32

bvF32ToUi64 :: RoundingMode -> BitVector 32 -> Result (BitVector 64)
bvF32ToUi64 = liftF1U f32ToUi64

bvF32ToI32 :: RoundingMode -> BitVector 32 -> Result (BitVector 32)
bvF32ToI32  = liftF1US f32ToI32

bvF32ToI64 :: RoundingMode -> BitVector 32 -> Result (BitVector 64)
bvF32ToI64  = liftF1US f32ToI64

bvF64ToUi32 :: RoundingMode -> BitVector 64 -> Result (BitVector 32)
bvF64ToUi32 = liftF1U f64ToUi32

bvF64ToUi64 :: RoundingMode -> BitVector 64 -> Result (BitVector 64)
bvF64ToUi64 = liftF1U f64ToUi64

bvF64ToI32 :: RoundingMode -> BitVector 64 -> Result (BitVector 32)
bvF64ToI32  = liftF1US f64ToI32

bvF64ToI64 :: RoundingMode -> BitVector 64 -> Result (BitVector 64)
bvF64ToI64  = liftF1US f64ToI64

-- Floating point to floating point conversions
bvF16ToF32 :: RoundingMode -> BitVector 16 -> Result (BitVector 32)
bvF16ToF32 = liftF1U f16ToF32

bvF16ToF64 :: RoundingMode -> BitVector 16 -> Result (BitVector 64)
bvF16ToF64 = liftF1U f16ToF64

bvF32ToF16 :: RoundingMode -> BitVector 32 -> Result (BitVector 16)
bvF32ToF16 = liftF1U f32ToF16

bvF32ToF64 :: RoundingMode -> BitVector 32 -> Result (BitVector 64)
bvF32ToF64 = liftF1U f32ToF64

bvF64ToF16 :: RoundingMode -> BitVector 64 -> Result (BitVector 16)
bvF64ToF16 = liftF1U f64ToF16

bvF64ToF32 :: RoundingMode -> BitVector 64 -> Result (BitVector 32)
bvF64ToF32 = liftF1U f64ToF32

-- 16-bit operations
bvF16RoundToInt :: RoundingMode -> BitVector 16 -> Result (BitVector 16)
bvF16RoundToInt = liftF1U f16RoundToInt

bvF16Add :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result (BitVector 16)
bvF16Add = liftF2 f16Add

bvF16Sub :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result (BitVector 16)
bvF16Sub = liftF2 f16Sub

bvF16Mul :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result (BitVector 16)
bvF16Mul = liftF2 f16Mul

bvF16MulAdd :: RoundingMode -> BitVector 16 -> BitVector 16 -> BitVector 16 -> Result (BitVector 16)
bvF16MulAdd = liftF3 f16MulAdd

bvF16Div :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result (BitVector 16)
bvF16Div = liftF2 f16Div

bvF16Rem :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result (BitVector 16)
bvF16Rem = liftF2 f16Rem

bvF16Sqrt :: RoundingMode -> BitVector 16 -> Result (BitVector 16)
bvF16Sqrt = liftF1U f16Sqrt

bvF16Eq :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result Bool
bvF16Eq = liftF2Bool f16Eq

bvF16Le :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result Bool
bvF16Le = liftF2Bool f16Le

bvF16Lt :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result Bool
bvF16Lt = liftF2Bool f16Lt

bvF16EqSignaling :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result Bool
bvF16EqSignaling = liftF2Bool f16EqSignaling

bvF16LeQuiet :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result Bool
bvF16LeQuiet = liftF2Bool f16LeQuiet

bvF16LtQuiet :: RoundingMode -> BitVector 16 -> BitVector 16 -> Result Bool
bvF16LtQuiet = liftF2Bool f16LtQuiet

bvF16IsSignalingNaN :: RoundingMode -> BitVector 16 -> Result Bool
bvF16IsSignalingNaN = liftF1Bool f16IsSignalingNaN

-- 32-bit operations
bvF32RoundToInt :: RoundingMode -> BitVector 32 -> Result (BitVector 32)
bvF32RoundToInt = liftF1U f32RoundToInt

bvF32Add :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result (BitVector 32)
bvF32Add = liftF2 f32Add

bvF32Sub :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result (BitVector 32)
bvF32Sub = liftF2 f32Sub

bvF32Mul :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result (BitVector 32)
bvF32Mul = liftF2 f32Mul

bvF32MulAdd :: RoundingMode -> BitVector 32 -> BitVector 32 -> BitVector 32 -> Result (BitVector 32)
bvF32MulAdd = liftF3 f32MulAdd

bvF32Div :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result (BitVector 32)
bvF32Div = liftF2 f32Div

bvF32Rem :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result (BitVector 32)
bvF32Rem = liftF2 f32Rem

bvF32Sqrt :: RoundingMode -> BitVector 32 -> Result (BitVector 32)
bvF32Sqrt = liftF1U f32Sqrt

bvF32Eq :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result Bool
bvF32Eq = liftF2Bool f32Eq

bvF32Le :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result Bool
bvF32Le = liftF2Bool f32Le

bvF32Lt :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result Bool
bvF32Lt = liftF2Bool f32Lt

bvF32EqSignaling :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result Bool
bvF32EqSignaling = liftF2Bool f32EqSignaling

bvF32LeQuiet :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result Bool
bvF32LeQuiet = liftF2Bool f32LeQuiet

bvF32LtQuiet :: RoundingMode -> BitVector 32 -> BitVector 32 -> Result Bool
bvF32LtQuiet = liftF2Bool f32LtQuiet

bvF32IsSignalingNaN :: RoundingMode -> BitVector 32 -> Result Bool
bvF32IsSignalingNaN = liftF1Bool f32IsSignalingNaN

-- 64-bit operations
bvF64RoundToInt :: RoundingMode -> BitVector 64 -> Result (BitVector 64)
bvF64RoundToInt = liftF1U f64RoundToInt

bvF64Add :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result (BitVector 64)
bvF64Add = liftF2 f64Add

bvF64Sub :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result (BitVector 64)
bvF64Sub = liftF2 f64Sub

bvF64Mul :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result (BitVector 64)
bvF64Mul = liftF2 f64Mul

bvF64MulAdd :: RoundingMode -> BitVector 64 -> BitVector 64 -> BitVector 64 -> Result (BitVector 64)
bvF64MulAdd = liftF3 f64MulAdd

bvF64Div :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result (BitVector 64)
bvF64Div = liftF2 f64Div

bvF64Rem :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result (BitVector 64)
bvF64Rem = liftF2 f64Rem

bvF64Sqrt :: RoundingMode -> BitVector 64 -> Result (BitVector 64)
bvF64Sqrt = liftF1U f64Sqrt

bvF64Eq :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result Bool
bvF64Eq = liftF2Bool f64Eq

bvF64Le :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result Bool
bvF64Le = liftF2Bool f64Le

bvF64Lt :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result Bool
bvF64Lt = liftF2Bool f64Lt

bvF64EqSignaling :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result Bool
bvF64EqSignaling = liftF2Bool f64EqSignaling

bvF64LeQuiet :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result Bool
bvF64LeQuiet = liftF2Bool f64LeQuiet

bvF64LtQuiet :: RoundingMode -> BitVector 64 -> BitVector 64 -> Result Bool
bvF64LtQuiet = liftF2Bool f64LtQuiet

bvF64IsSignalingNaN :: RoundingMode -> BitVector 64 -> Result Bool
bvF64IsSignalingNaN = liftF1Bool f64IsSignalingNaN

-- TODO: The following commented code outlines a strategy for unifying all floating
-- point ops into individual functions (so bvFAdd for 16-, 32-, and 64-bit
-- add). Since this probably isn't necessary for my purposes, and adds a lot of
-- type-level cruft and overhead, I am abandoning it and opting for the simpler
-- strategy of writing individual functions for the 16-, 32-, and 64-bit cases.

-- data FloatType = Float16
--                | Float32
--                | Float64

-- type Float16 = 'Float16
-- type Float32 = 'Float32
-- type Float64 = 'Float64

-- data FloatTypeRepr :: FloatType -> * where
--   Float16Repr :: FloatTypeRepr Float16
--   Float32Repr :: FloatTypeRepr Float32
--   Float64Repr :: FloatTypeRepr Float64

-- instance KnownRepr FloatTypeRepr Float16 where knownRepr = Float16Repr
-- instance KnownRepr FloatTypeRepr Float32 where knownRepr = Float32Repr
-- instance KnownRepr FloatTypeRepr Float64 where knownRepr = Float64Repr

-- type family FloatWidth (ft :: FloatType) :: Nat where
--   FloatWidth Float16 = 16
--   FloatWidth Float32 = 32
--   FloatWidth Float64 = 64

-- type family FloatWord (ft :: FloatType) :: * where
--   FloatWord Float16 = Word16
--   FloatWord Float32 = Word32
--   FloatWord Float64 = Word64

-- data FloatBV (ft :: FloatType) where
--   FloatBV :: FloatTypeRepr ft -> BitVector (FloatWidth ft) -> FloatBV ft

-- bvBinaryOpFloat :: (RoundingMode -> Word16 -> Word16 -> Result Word16)
--                 -> (RoundingMode -> Word32 -> Word32 -> Result Word32)
--                 -> (RoundingMode -> Word64 -> Word64 -> Result Word64)
--                 -> RoundingMode -> FloatBV ft -> FloatBV ft -> Result (FloatBV ft)
-- bvBinaryOpFloat flop16 flop32 flop64 rm (FloatBV fRepr (BV wRepr x)) (FloatBV _ (BV _ y)) =
--   case fRepr of
--     Float16Repr ->
--       let Result wordVal flags = flop16 rm (fromIntegral x) (fromIntegral y)
--       in Result (FloatBV Float16Repr (BV wRepr (fromIntegral wordVal))) flags
--     Float32Repr ->
--       let Result wordVal flags = flop32 rm (fromIntegral x) (fromIntegral y)
--       in Result (FloatBV Float32Repr (BV wRepr (fromIntegral wordVal))) flags
--     Float64Repr ->
--       let Result wordVal flags = flop64 rm (fromIntegral x) (fromIntegral y)
--       in Result (FloatBV Float64Repr (BV wRepr (fromIntegral wordVal))) flags

-- bvAddF :: RoundingMode -> FloatBV ft -> FloatBV ft -> Result (FloatBV ft)
-- bvAddF = bvBinaryOpFloat f16Add f32Add f64Add

-- instance Show (FloatBitVector ft) where
--   show (FloatBitVector bv) = show bv

-- instance ShowF FloatBitVector

