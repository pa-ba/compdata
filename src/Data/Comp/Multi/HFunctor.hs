{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, ScopedTypeVariables, GADTs, MultiParamTypeClasses, UndecidableInstances, IncoherentInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.HFunctor
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

module Data.Comp.Multi.HFunctor
    (
     HFunctor (..),
     HFoldable (..),
     HTraversable (..),
     (:->),
     (:=>),
     NatM,
     I (..),
     K (..),
     A (..),
     kfoldr,
     kfoldl,
     htoList
     ) where

import Data.Monoid
import Data.Maybe
import Control.Applicative

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


-- | Higher-order functors that can be folded.
--
-- Minimal complete definition: 'hfoldMap' or 'hfoldr'.
class HFunctor h => HFoldable h where
    hfold :: Monoid m => h (K m) :=> m
    hfold = hfoldMap unK

    hfoldMap :: Monoid m => (a :=> m) -> h a :=> m
    hfoldMap f = hfoldr (mappend . f) mempty

    hfoldr :: (a :=> b -> b) -> b -> h a :=> b
    hfoldr f z t = appEndo (hfoldMap (Endo . f) t) z

    hfoldl :: (b -> a :=> b) -> b -> h a :=> b
    hfoldl f z t = appEndo (getDual (hfoldMap (Dual . Endo . flip f) t)) z


    hfoldr1 :: forall a. (a -> a -> a) -> h (K a) :=> a
    hfoldr1 f xs = fromMaybe (error "hfoldr1: empty structure")
                   (hfoldr mf Nothing xs)
          where mf :: K a :=> Maybe a -> Maybe a
                mf (K x) Nothing = Just x
                mf (K x) (Just y) = Just (f x y)

    hfoldl1 :: forall a . (a -> a -> a) -> h (K a) :=> a
    hfoldl1 f xs = fromMaybe (error "hfoldl1: empty structure")
                   (hfoldl mf Nothing xs)
          where mf :: Maybe a -> K a :=> Maybe a
                mf Nothing (K y) = Just y
                mf (Just x) (K y) = Just (f x y)

htoList :: (HFoldable f) => f a :=> [A a]
htoList = hfoldr (\ n l ->  A n : l) []
    
kfoldr :: (HFoldable f) => (a -> b -> b) -> b -> f (K a) :=> b
kfoldr f = hfoldr (\ (K x) y -> f x y)


kfoldl :: (HFoldable f) => (b -> a -> b) -> b -> f (K a) :=> b
kfoldl f = hfoldl (\ x (K y) -> f x y)


class HFoldable t => HTraversable t where

    -- | Map each element of a structure to a monadic action, evaluate
    -- these actions from left to right, and collect the results.
    --
    -- Alternative type in terms of natural transformations using
    -- functor composition @:.:@:
    --
    -- @hmapM :: Monad m => (a :-> m :.: b) -> t a :-> m :.: (t b)@
    hmapM :: (Monad m) => NatM m a b -> NatM m (t a) (t b)

    htraverse :: (Applicative f) => NatM f a b -> NatM f (t a) (t b)