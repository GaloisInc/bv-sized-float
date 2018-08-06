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
  -- , evalBVFloatApp
  -- , evalBVFloatAppM
  -- -- * Smart constructors
  -- , BVFloatExpr(..)
  -- -- * Integer to float conversions
  ) where

import GHC.TypeLits

data BVFloatApp (expr :: Nat -> *) (w :: Nat) where
  Ui16ToF16App :: !(expr 16) -> BVFloatApp expr w
