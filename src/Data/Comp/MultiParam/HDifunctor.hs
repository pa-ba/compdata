{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, RankNTypes,
  TypeOperators, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.HDifunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines higher-order difunctors, a hybrid between higher-order
-- functors (Johann, Ghani, POPL '08), and difunctors (Meijer, Hutton, FPCA
-- '95). Higher-order difunctors are used to define signatures for
-- compositional parametric generalised data types.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.HDifunctor
    (
     HDifunctor (..),
     HFunctor (..),
     I (..),
     K (..),
     A (..),
     (:->),
     NatM
    ) where

import Data.Comp.Multi.Functor (HFunctor (..))

-- | The identity functor.
data I a = I {unI :: a}

-- | The parametrised constant functor.
data K a i = K {unK :: a}

instance Functor I where
    fmap f (I x) = I (f x)

instance Functor (K a) where
    fmap _ (K x) = K x

data A f = forall i. A {unA :: f i}

instance Eq a => Eq (K a i) where
    K x == K y = x == y
    K x /= K y = x /= y

instance Ord a => Ord (K a i) where
    K x < K y = x < y
    K x > K y = x > y
    K x <= K y = x <= y
    K x >= K y = x >= y
    min (K x) (K y) = K $ min x y
    max (K x) (K y) = K $ max x y
    compare (K x) (K y) = compare x y

infixr 0 :-> -- same precedence as function space operator ->

-- |This type represents natural transformations.
type f :-> g = forall i . f i -> g i

-- |This type represents monadic natural transformations.
type NatM m f g = forall i. f i -> m (g i)

-- | This class represents higher-order difunctors.
class HDifunctor f where
    hdimap :: (a :-> b) -> (c :-> d) -> f b c :-> f a d

-- |A higher-order difunctor gives rise to a higher-order functor when
-- restricted to a particular contravariant argument.
instance HDifunctor f => HFunctor (f a) where
    hfmap = hdimap id