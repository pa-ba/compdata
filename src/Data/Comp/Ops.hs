{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
             ScopedTypeVariables, FunctionalDependencies, UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Ops
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on functors.
--
--------------------------------------------------------------------------------

module Data.Comp.Ops where

import Data.Foldable
import Data.Traversable

import Control.Applicative
import Control.Monad hiding (sequence, mapM)

import Prelude hiding (foldl, mapM, sequence, foldl1, foldr1, foldr)


-- Sums

infixr 6 :+:


-- |Formal sum of signatures (functors).
data (f :+: g) e = Inl (f e)
                 | Inr (g e)

instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (Inl e) = Inl (fmap f e)
    fmap f (Inr e) = Inr (fmap f e)

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
    fold (Inl e) = fold e
    fold (Inr e) = fold e
    foldMap f (Inl e) = foldMap f e
    foldMap f (Inr e) = foldMap f e
    foldr f b (Inl e) = foldr f b e
    foldr f b (Inr e) = foldr f b e
    foldl f b (Inl e) = foldl f b e
    foldl f b (Inr e) = foldl f b e
    foldr1 f (Inl e) = foldr1 f e
    foldr1 f (Inr e) = foldr1 f e
    foldl1 f (Inl e) = foldl1 f e
    foldl1 f (Inr e) = foldl1 f e

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
    traverse f (Inl e) = Inl <$> traverse f e
    traverse f (Inr e) = Inr <$> traverse f e
    sequenceA (Inl e) = Inl <$> sequenceA e
    sequenceA (Inr e) = Inr <$> sequenceA e
    mapM f (Inl e) = Inl `liftM` mapM f e
    mapM f (Inr e) = Inr `liftM` mapM f e
    sequence (Inl e) = Inl `liftM` sequence e
    sequence (Inr e) = Inr `liftM` sequence e

-- | Signature containment relation for automatic injections. The left-hand must
-- be an atomic signature, where as the right-hand side must have a list-like
-- structure. Examples include @f :<: f :+: g@ and @g :<: f :+: (g :+: h)@,
-- non-examples include @f :+: g :<: f :+: (g :+: h)@ and
-- @f :<: (f :+: g) :+: h@.
class sub :<: sup where
  inj :: sub a -> sup a
  proj :: sup a -> Maybe (sub a)

instance (:<:) f f where
    inj = id
    proj = Just

instance (:<:) f (f :+: g) where
    inj = Inl
    proj (Inl x) = Just x
    proj (Inr _) = Nothing

instance (f :<: g) => (:<:) f (h :+: g) where
    inj = Inr . inj
    proj (Inr x) = proj x
    proj (Inl _) = Nothing

-- Products

infixr 8 :*:

-- |Formal product of signatures (functors).
data (f :*: g) a = f a :*: g a


ffst :: (f :*: g) a -> f a
ffst (x :*: _) = x

fsnd :: (f :*: g) a -> g a
fsnd (_ :*: x) = x

-- Constant Products

infixr 7 :&:

{-| This data type adds a constant product to a signature.  -}

data (f :&: a) e = f e :&: a


instance (Functor f) => Functor (f :&: a) where
    fmap f (v :&: c) = fmap f v :&: c

instance (Foldable f) => Foldable (f :&: a) where
    fold (v :&: _) = fold v
    foldMap f (v :&: _) = foldMap f v
    foldr f e (v :&: _) = foldr f e v
    foldl f e (v :&: _) = foldl f e v
    foldr1 f (v :&: _) = foldr1 f v
    foldl1 f (v :&: _) = foldl1 f v

instance (Traversable f) => Traversable (f :&: a) where
    traverse f (v :&: c) = liftA (:&: c) (traverse f v)
    sequenceA (v :&: c) = liftA (:&: c)(sequenceA v)
    mapM f (v :&: c) = liftM (:&: c) (mapM f v)
    sequence (v :&: c) = liftM (:&: c) (sequence v)

{-| This class defines how to distribute a product over a sum of
signatures. -}

class DistProd s p s' | s' -> s, s' -> p where
    {-| Inject a product value over a signature. -}
    injectP :: p -> s a -> s' a
    {-| Project a product value from a signature. -}
    projectP :: s' a -> (s a, p)


class RemoveP s s' | s -> s'  where
    {-| Remove products from a signature. -}
    removeP :: s a -> s' a

instance (RemoveP s s') => RemoveP (f :&: p :+: s) (f :+: s') where
    removeP (Inl (v :&: _)) = Inl v
    removeP (Inr v) = Inr $ removeP v


instance RemoveP (f :&: p) f where
    removeP (v :&: _) = v


instance DistProd f p (f :&: p) where

    injectP c v = v :&: c

    projectP (v :&: p) = (v,p)


instance (DistProd s p s') => DistProd (f :+: s) p ((f :&: p) :+: s') where


    injectP c (Inl v) = Inl (v :&: c)
    injectP c (Inr v) = Inr $ injectP c v

    projectP (Inl (v :&: p)) = (Inl v,p)
    projectP (Inr v) = let (v',p) = projectP v
                       in  (Inr v',p)