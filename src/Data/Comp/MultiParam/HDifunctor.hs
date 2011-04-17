{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, RankNTypes,
  TypeOperators, GADTs, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.HDifunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines difunctors (Meijer, Hutton, FPCA '95), i.e. binary type
-- constructors that are contravariant in the first argument and covariant in
-- the second argument.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.HDifunctor
    (
     HDifunctor (..),
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

-- | This type represents natural transformations.
type f :-> g = forall i . f i -> g i

type NatM m f g = forall i. f i -> m (g i)

-- | This class represents difunctors, i.e. binary type constructors that are
-- contravariant in the first argument and covariant in the second argument.
class HDifunctor f where
    dimap :: (a :-> b) -> (c :-> d) -> f b c :-> f a d

instance HDifunctor f => HFunctor (f a) where
    hfmap = dimap id