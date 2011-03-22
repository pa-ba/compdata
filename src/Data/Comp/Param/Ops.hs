{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
  FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
  ScopedTypeVariables, FunctionalDependencies, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ops
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Ops where

import Data.Comp.Param.Functor
import Data.Comp.Param.Traversable

import Control.Monad hiding (sequence, mapM)

import Prelude hiding (foldl, mapM, sequence, foldl1, foldr1, foldr)


-- Sums

infixr 6 :+:


-- |Formal sum of signatures (functors).
data (f :+: g) a e = Inl (f a e)
                   | Inr (g a e)

instance (Difunctor f, Difunctor g) => Difunctor (f :+: g) where
    dimap f g (Inl e) = Inl (dimap f g e)
    dimap f g (Inr e) = Inr (dimap f g e)

{-instance (Difoldable f, Difoldable g) => Difoldable (f :+: g) where
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
-}
instance (Ditraversable f, Ditraversable g) => Ditraversable (f :+: g) where
{-    traverse f (Inl e) = Inl <$> traverse f e
    traverse f (Inr e) = Inr <$> traverse f e
    sequenceA (Inl e) = Inl <$> sequenceA e
    sequenceA (Inr e) = Inr <$> sequenceA e-}
    dimapM f (Inl e) = Inl `liftM` dimapM f e
    dimapM f (Inr e) = Inr `liftM` dimapM f e
    disequence (Inl e) = Inl `liftM` disequence e
    disequence (Inr e) = Inr `liftM` disequence e

-- | Signature containment relation for automatic injections. The left-hand must
-- be an atomic signature, where as the right-hand side must have a list-like
-- structure. Examples include @f :<: f :+: g@ and @g :<: f :+: (g :+: h)@,
-- non-examples include @f :+: g :<: f :+: (g :+: h)@ and
-- @f :<: (f :+: g) :+: h@.
class sub :<: sup where
  inj :: sub a b -> sup a b
  proj :: sup a b -> Maybe (sub a b)

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

-- |Formal product of signatures (difunctors).
data (f :*: g) a e = f a e :*: g a e


ffst :: (f :*: g) a e -> f a e
ffst (x :*: _) = x

fsnd :: (f :*: g) a e -> g a e
fsnd (_ :*: x) = x

-- Constant Products

infixr 7 :&:

{-| This data type adds a constant product to a signature.  -}

data (f :&: p) a e = f a e :&: p


instance (Difunctor f) => Difunctor (f :&: a) where
    dimap f g (v :&: c) = dimap f g v :&: c

{-instance (Foldable f) => Foldable (f :&: a) where
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
    sequence (v :&: c) = liftM (:&: c) (sequence v)-}

{-| This class defines how to distribute a product over a sum of
signatures. -}

class DistProd s p s' | s' -> s, s' -> p where
    {-| Inject a product value over a signature. -}
    injectP :: p -> s a e -> s' a e
    {-| Project a product value from a signature. -}
    projectP :: s' a e -> (s a e, p)


class RemoveP s s' | s -> s'  where
    {-| Remove products from a signature. -}
    removeP :: s a e -> s' a e

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