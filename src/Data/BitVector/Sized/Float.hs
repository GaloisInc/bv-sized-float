{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
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
    ui32ToF16
  , ui32ToF32
  , ui32ToF64
  , i32ToF16
  , i32ToF32
  , i32ToF64
  , ui64ToF16
  , ui64ToF32
  , ui64ToF64
  , i64ToF16
  , i64ToF32
  , i64ToF64

    -- * Floating point to integer conversions
  , f16ToUi32
  , f16ToUi64
  , f16ToI32
  , f16ToI64
  , f32ToUi32
  , f32ToUi64
  , f32ToI32
  , f32ToI64
  , f64ToUi32
  , f64ToUi64
  , f64ToI32
  , f64ToI64

    -- * Floating point to floating point conversions
  , f16ToF32
  , f16ToF64
  , f32ToF16
  , f32ToF64
  , f64ToF16
  , f64ToF32


    -- * 16-bit operations
  , f16RoundToInt
  , f16Add
  , f16Sub
  , f16Mul
  , f16MulAdd
  , f16Div
  , f16Rem
  , f16Sqrt
  , f16Eq
  , f16Le
  , f16Lt
  , f16EqSignaling
  , f16LeQuiet
  , f16LtQuiet
  , f16IsSignalingNaN

    -- * 32-bit operations
  , f32RoundToInt
  , f32Add
  , f32Sub
  , f32Mul
  , f32MulAdd
  , f32Div
  , f32Rem
  , f32Sqrt
  , f32Eq
  , f32Le
  , f32Lt
  , f32EqSignaling
  , f32LeQuiet
  , f32LtQuiet
  , f32IsSignalingNaN

    -- * 64-bit operations
  , f64RoundToInt
  , f64Add
  , f64Sub
  , f64Mul
  , f64MulAdd
  , f64Div
  , f64Rem
  , f64Sqrt
  , f64Eq
  , f64Le
  , f64Lt
  , f64EqSignaling
  , f64LeQuiet
  , f64LtQuiet
  , f64IsSignalingNaN
  ) where

import qualified Data.BitVector.Sized as BV
import Data.Int ( Int16, Int32, Int64 )
import Data.Kind ( Type )
import Data.Parameterized ( knownNat )
import Data.Type.Equality
    ( type (:~:)(Refl), TestEquality(testEquality) )
import Data.Word ( Word16, Word32, Word64 )
import GHC.TypeNats ( type (<=), KnownNat, Nat )
import qualified SoftFloat as SF

type family WordType (n :: Nat) :: Type where
  WordType 16 = Word16
  WordType 32 = Word32
  WordType 64 = Word64

type family IntType (n :: Nat) :: Type where
  IntType 16 = Int16
  IntType 32 = Int32
  IntType 64 = Int64

word :: forall w. KnownNat w => WordType w -> BV.BV w
word =
  let nw = knownNat @w in
  case nw of
  _ | Just Refl <- testEquality nw (knownNat @16) -> BV.word16
  _ | Just Refl <- testEquality nw (knownNat @32) -> BV.word32
  _ | Just Refl <- testEquality nw (knownNat @64) -> BV.word64
  _ | otherwise -> error ("Unhandled WordType: " ++ show nw ++ ". Please report.")

int :: forall w. KnownNat w => IntType w -> BV.BV w
int =
  let nw = knownNat @w in
  case nw of
  _ | Just Refl <- testEquality nw (knownNat @16) -> BV.int16
  _ | Just Refl <- testEquality nw (knownNat @32) -> BV.int32
  _ | Just Refl <- testEquality nw (knownNat @64) -> BV.int64
  _ | otherwise -> error ("Unhandled IntType: " ++ show nw ++ ". Please report.")

liftF1U :: (KnownNat w, Integral (WordType w),
            KnownNat w', Integral (WordType w'))
        => (SF.RoundingMode -> WordType w -> SF.Result (WordType w'))
        -> SF.RoundingMode -> BV.BV w -> SF.Result (BV.BV w')
liftF1U flop1 rm bv =
  let SF.Result f fFlags = flop1 rm (fromIntegral $ BV.asUnsigned bv)
  in  SF.Result (word f) fFlags

liftF1SU :: (KnownNat w, Integral (IntType w), 1 <= w,
            KnownNat w', Integral (WordType w'))
        => (SF.RoundingMode -> IntType w -> SF.Result (WordType w'))
        -> SF.RoundingMode -> BV.BV w -> SF.Result (BV.BV w')
liftF1SU flop1 rm bv =
  let SF.Result f fFlags = flop1 rm (fromIntegral $ BV.asSigned knownNat bv)
  in  SF.Result (word f) fFlags

liftF1US :: (KnownNat w, Integral (WordType w),
            KnownNat w', Integral (IntType w'))
        => (SF.RoundingMode -> WordType w -> SF.Result (IntType w'))
        -> SF.RoundingMode -> BV.BV w -> SF.Result (BV.BV w')
liftF1US flop1 rm bv =
  let SF.Result f fFlags = flop1 rm (fromIntegral $ BV.asUnsigned bv)
  in  SF.Result (int f) fFlags

liftF1Bool :: (KnownNat w, Integral (WordType w))
           => (WordType w -> SF.Result Bool)
           -> BV.BV w -> SF.Result Bool
liftF1Bool flop1 bv = flop1 (fromIntegral $ BV.asUnsigned bv)

liftF2 :: (KnownNat w, Integral (WordType w))
       => (SF.RoundingMode -> WordType w -> WordType w -> SF.Result (WordType w))
       -> SF.RoundingMode -> BV.BV w -> BV.BV w -> SF.Result (BV.BV w)
liftF2 flop2 rm bv1 bv2 =
  let SF.Result f fFlags = flop2 rm (fromIntegral $ BV.asUnsigned bv1) (fromIntegral $ BV.asUnsigned bv2)
  in  SF.Result (word f) fFlags

liftF2Bool :: (KnownNat w, Integral (WordType w))
           => (WordType w -> WordType w -> SF.Result Bool)
           -> BV.BV w -> BV.BV w -> SF.Result Bool
liftF2Bool flop2 bv1 bv2 = flop2 (fromIntegral $ BV.asUnsigned bv1) (fromIntegral $ BV.asUnsigned bv2)

liftF3 :: (KnownNat w, Integral (WordType w))
       => (SF.RoundingMode -> WordType w -> WordType w -> WordType w -> SF.Result (WordType w))
       -> SF.RoundingMode -> BV.BV w -> BV.BV w -> BV.BV w -> SF.Result (BV.BV w)
liftF3 flop3 rm bv1 bv2 bv3 =
  let SF.Result f fFlags = flop3 rm (fromIntegral $ BV.asUnsigned bv1) (fromIntegral $ BV.asUnsigned bv2) (fromIntegral $ BV.asUnsigned bv3)
  in  SF.Result (word f) fFlags

-- Integer to floating point

ui32ToF16 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 16)
ui32ToF16 = liftF1U SF.ui32ToF16

ui32ToF32 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 32)
ui32ToF32 = liftF1U SF.ui32ToF32

ui32ToF64 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 64)
ui32ToF64 = liftF1U SF.ui32ToF64

i32ToF16 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 16)
i32ToF16 = liftF1SU SF.i32ToF16

i32ToF32 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 32)
i32ToF32 = liftF1SU SF.i32ToF32

i32ToF64 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 64)
i32ToF64 = liftF1SU SF.i32ToF64

ui64ToF16 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 16)
ui64ToF16 = liftF1U SF.ui64ToF16

ui64ToF32 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 32)
ui64ToF32 = liftF1U SF.ui64ToF32

ui64ToF64 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 64)
ui64ToF64 = liftF1U SF.ui64ToF64

i64ToF16 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 16)
i64ToF16 = liftF1SU SF.i64ToF16

i64ToF32 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 32)
i64ToF32 = liftF1SU SF.i64ToF32

i64ToF64 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 64)
i64ToF64 = liftF1SU SF.i64ToF64

-- Floating point to integer

f16ToUi32 :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 32)
f16ToUi32 = liftF1U SF.f16ToUi32

f16ToUi64 :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 64)
f16ToUi64 = liftF1U SF.f16ToUi64

f16ToI32 :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 32)
f16ToI32  = liftF1US SF.f16ToI32

f16ToI64 :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 64)
f16ToI64  = liftF1US SF.f16ToI64

f32ToUi32 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 32)
f32ToUi32 = liftF1U SF.f32ToUi32

f32ToUi64 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 64)
f32ToUi64 = liftF1U SF.f32ToUi64

f32ToI32 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 32)
f32ToI32  = liftF1US SF.f32ToI32

f32ToI64 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 64)
f32ToI64  = liftF1US SF.f32ToI64

f64ToUi32 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 32)
f64ToUi32 = liftF1U SF.f64ToUi32

f64ToUi64 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 64)
f64ToUi64 = liftF1U SF.f64ToUi64

f64ToI32 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 32)
f64ToI32  = liftF1US SF.f64ToI32

f64ToI64 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 64)
f64ToI64  = liftF1US SF.f64ToI64

-- Floating point to floating point conversions
f16ToF32 :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 32)
f16ToF32 = liftF1U SF.f16ToF32

f16ToF64 :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 64)
f16ToF64 = liftF1U SF.f16ToF64

f32ToF16 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 16)
f32ToF16 = liftF1U SF.f32ToF16

f32ToF64 :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 64)
f32ToF64 = liftF1U SF.f32ToF64

f64ToF16 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 16)
f64ToF16 = liftF1U SF.f64ToF16

f64ToF32 :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 32)
f64ToF32 = liftF1U SF.f64ToF32

-- 16-bit operations
f16RoundToInt :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 16)
f16RoundToInt = liftF1U SF.f16RoundToInt

f16Add :: SF.RoundingMode -> BV.BV 16 -> BV.BV 16 -> SF.Result (BV.BV 16)
f16Add = liftF2 SF.f16Add

f16Sub :: SF.RoundingMode -> BV.BV 16 -> BV.BV 16 -> SF.Result (BV.BV 16)
f16Sub = liftF2 SF.f16Sub

f16Mul :: SF.RoundingMode -> BV.BV 16 -> BV.BV 16 -> SF.Result (BV.BV 16)
f16Mul = liftF2 SF.f16Mul

f16MulAdd :: SF.RoundingMode -> BV.BV 16 -> BV.BV 16 -> BV.BV 16 -> SF.Result (BV.BV 16)
f16MulAdd = liftF3 SF.f16MulAdd

f16Div :: SF.RoundingMode -> BV.BV 16 -> BV.BV 16 -> SF.Result (BV.BV 16)
f16Div = liftF2 SF.f16Div

f16Rem :: SF.RoundingMode -> BV.BV 16 -> BV.BV 16 -> SF.Result (BV.BV 16)
f16Rem = liftF2 SF.f16Rem

f16Sqrt :: SF.RoundingMode -> BV.BV 16 -> SF.Result (BV.BV 16)
f16Sqrt = liftF1U SF.f16Sqrt

f16Eq :: BV.BV 16 -> BV.BV 16 -> SF.Result Bool
f16Eq = liftF2Bool SF.f16Eq

f16Le :: BV.BV 16 -> BV.BV 16 -> SF.Result Bool
f16Le = liftF2Bool SF.f16Le

f16Lt :: BV.BV 16 -> BV.BV 16 -> SF.Result Bool
f16Lt = liftF2Bool SF.f16Lt

f16EqSignaling :: BV.BV 16 -> BV.BV 16 -> SF.Result Bool
f16EqSignaling = liftF2Bool SF.f16EqSignaling

f16LeQuiet :: BV.BV 16 -> BV.BV 16 -> SF.Result Bool
f16LeQuiet = liftF2Bool SF.f16LeQuiet

f16LtQuiet :: BV.BV 16 -> BV.BV 16 -> SF.Result Bool
f16LtQuiet = liftF2Bool SF.f16LtQuiet

f16IsSignalingNaN :: BV.BV 16 -> SF.Result Bool
f16IsSignalingNaN = liftF1Bool SF.f16IsSignalingNaN

-- 32-bit operations
f32RoundToInt :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 32)
f32RoundToInt = liftF1U SF.f32RoundToInt

f32Add :: SF.RoundingMode -> BV.BV 32 -> BV.BV 32 -> SF.Result (BV.BV 32)
f32Add = liftF2 SF.f32Add

f32Sub :: SF.RoundingMode -> BV.BV 32 -> BV.BV 32 -> SF.Result (BV.BV 32)
f32Sub = liftF2 SF.f32Sub

f32Mul :: SF.RoundingMode -> BV.BV 32 -> BV.BV 32 -> SF.Result (BV.BV 32)
f32Mul = liftF2 SF.f32Mul

f32MulAdd :: SF.RoundingMode -> BV.BV 32 -> BV.BV 32 -> BV.BV 32 -> SF.Result (BV.BV 32)
f32MulAdd = liftF3 SF.f32MulAdd

f32Div :: SF.RoundingMode -> BV.BV 32 -> BV.BV 32 -> SF.Result (BV.BV 32)
f32Div = liftF2 SF.f32Div

f32Rem :: SF.RoundingMode -> BV.BV 32 -> BV.BV 32 -> SF.Result (BV.BV 32)
f32Rem = liftF2 SF.f32Rem

f32Sqrt :: SF.RoundingMode -> BV.BV 32 -> SF.Result (BV.BV 32)
f32Sqrt = liftF1U SF.f32Sqrt

f32Eq :: BV.BV 32 -> BV.BV 32 -> SF.Result Bool
f32Eq = liftF2Bool SF.f32Eq

f32Le :: BV.BV 32 -> BV.BV 32 -> SF.Result Bool
f32Le = liftF2Bool SF.f32Le

f32Lt :: BV.BV 32 -> BV.BV 32 -> SF.Result Bool
f32Lt = liftF2Bool SF.f32Lt

f32EqSignaling :: BV.BV 32 -> BV.BV 32 -> SF.Result Bool
f32EqSignaling = liftF2Bool SF.f32EqSignaling

f32LeQuiet :: BV.BV 32 -> BV.BV 32 -> SF.Result Bool
f32LeQuiet = liftF2Bool SF.f32LeQuiet

f32LtQuiet :: BV.BV 32 -> BV.BV 32 -> SF.Result Bool
f32LtQuiet = liftF2Bool SF.f32LtQuiet

f32IsSignalingNaN :: BV.BV 32 -> SF.Result Bool
f32IsSignalingNaN = liftF1Bool SF.f32IsSignalingNaN

-- 64-bit operations
f64RoundToInt :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 64)
f64RoundToInt = liftF1U SF.f64RoundToInt

f64Add :: SF.RoundingMode -> BV.BV 64 -> BV.BV 64 -> SF.Result (BV.BV 64)
f64Add = liftF2 SF.f64Add

f64Sub :: SF.RoundingMode -> BV.BV 64 -> BV.BV 64 -> SF.Result (BV.BV 64)
f64Sub = liftF2 SF.f64Sub

f64Mul :: SF.RoundingMode -> BV.BV 64 -> BV.BV 64 -> SF.Result (BV.BV 64)
f64Mul = liftF2 SF.f64Mul

f64MulAdd :: SF.RoundingMode -> BV.BV 64 -> BV.BV 64 -> BV.BV 64 -> SF.Result (BV.BV 64)
f64MulAdd = liftF3 SF.f64MulAdd

f64Div :: SF.RoundingMode -> BV.BV 64 -> BV.BV 64 -> SF.Result (BV.BV 64)
f64Div = liftF2 SF.f64Div

f64Rem :: SF.RoundingMode -> BV.BV 64 -> BV.BV 64 -> SF.Result (BV.BV 64)
f64Rem = liftF2 SF.f64Rem

f64Sqrt :: SF.RoundingMode -> BV.BV 64 -> SF.Result (BV.BV 64)
f64Sqrt = liftF1U SF.f64Sqrt

f64Eq :: BV.BV 64 -> BV.BV 64 -> SF.Result Bool
f64Eq = liftF2Bool SF.f64Eq

f64Le :: BV.BV 64 -> BV.BV 64 -> SF.Result Bool
f64Le = liftF2Bool SF.f64Le

f64Lt :: BV.BV 64 -> BV.BV 64 -> SF.Result Bool
f64Lt = liftF2Bool SF.f64Lt

f64EqSignaling :: BV.BV 64 -> BV.BV 64 -> SF.Result Bool
f64EqSignaling = liftF2Bool SF.f64EqSignaling

f64LeQuiet :: BV.BV 64 -> BV.BV 64 -> SF.Result Bool
f64LeQuiet = liftF2Bool SF.f64LeQuiet

f64LtQuiet :: BV.BV 64 -> BV.BV 64 -> SF.Result Bool
f64LtQuiet = liftF2Bool SF.f64LtQuiet

f64IsSignalingNaN :: BV.BV 64 -> SF.Result Bool
f64IsSignalingNaN = liftF1Bool SF.f64IsSignalingNaN

-- TODO: The following commented code outlines a strategy for unifying all floating
-- point ops into individual functions (so fAdd for 16-, 32-, and 64-bit
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
--   FloatBV :: FloatTypeRepr ft -> BV.BV (FloatWidth ft) -> FloatBV ft

-- bvBinaryOpFloat :: (SF.RoundingMode -> Word16 -> Word16 -> SF.Result Word16)
--                 -> (SF.RoundingMode -> Word32 -> Word32 -> SF.Result Word32)
--                 -> (SF.RoundingMode -> Word64 -> Word64 -> SF.Result Word64)
--                 -> SF.RoundingMode -> FloatBV ft -> FloatBV ft -> SF.Result (FloatBV ft)
-- bvBinaryOpFloat flop16 flop32 flop64 rm (FloatBV fRepr (BV.BV wRepr x)) (FloatBV _ (BV.BV _ y)) =
--   case fRepr of
--     Float16Repr ->
--       let SF.Result wordVal flags = flop16 rm (fromIntegral x) (fromIntegral y)
--       in SF.Result (FloatBV Float16Repr (BV.BV wRepr (fromIntegral wordVal))) flags
--     Float32Repr ->
--       let SF.Result wordVal flags = flop32 rm (fromIntegral x) (fromIntegral y)
--       in SF.Result (FloatBV Float32Repr (BV.BV wRepr (fromIntegral wordVal))) flags
--     Float64Repr ->
--       let SF.Result wordVal flags = flop64 rm (fromIntegral x) (fromIntegral y)
--       in SF.Result (FloatBV Float64Repr (BV.BV wRepr (fromIntegral wordVal))) flags

-- bvAddF :: SF.RoundingMode -> FloatBV ft -> FloatBV ft -> SF.Result (FloatBV ft)
-- bvAddF = bvBinaryOpFloat f16Add SF.f32Add SF.f64Add

-- instance Show (FloatBitVector ft) where
--   show (FloatBitVector bv) = show bv

-- instance ShowF FloatBitVector
