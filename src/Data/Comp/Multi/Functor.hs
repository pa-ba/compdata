{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, ScopedTypeVariables, GADTs, MultiParamTypeClasses, UndecidableInstances, IncoherentInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Functor
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines higher-order functors (Johann, Ghani, POPL
-- '08), i.e. endofunctors on the category of endofunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Functor
    (
     HFunctor (..),
     (:->),
     (:=>),
     NatM,
     I (..),
     K (..),
     A (..),
     (:.:)(..)
     ) where

-- | The identity Functor.
data I a = I {unI :: a}

-- | The parametrised constant functor.
data K a b = K {unK :: a}

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
infixr 0 :=> -- same precedence as function space operator ->

-- | This type represents natural transformations.
type f :-> g = forall i . f i -> g i

-- | This type represents co-cones from @f@ to @a@. @f :=> a@ is
-- isomorphic to f :-> K a
type f :=> a = forall i . f i -> a


type NatM m f g = forall i. f i -> m (g i)

-- | This class represents higher-order functors (Johann, Ghani, POPL
-- '08) which are endofunctors on the category of endofunctors.
class HFunctor h where
    -- A higher-order functor @f@ maps every functor @g@ to a
    -- functor @f g@.
    --
    -- @ffmap :: (Functor g) => (a -> b) -> f g a -> f g b@
    -- 
    -- We omit this, as it does not work for GADTs (see Johand and
    -- Ghani 2008).

    -- | A higher-order functor @f@ also maps a natural transformation
    -- @g :-> h@ to a natural transformation @f g :-> f h@
    hfmap :: (f :-> g) -> h f :-> h g

infixl 5 :.:

-- | This data type denotes the composition of two functor families.
data (f :.: g) e t = Comp f (g e) t