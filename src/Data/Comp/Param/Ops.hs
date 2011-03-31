{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, UndecidableInstances, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ops
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
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
import Control.Monad (liftM)


-- Sums
infixr 6 :+:

-- |Formal sum of signatures (difunctors).
data (f :+: g) a b = Inl (f a b)
                   | Inr (g a b)

instance (Difunctor f, Difunctor g) => Difunctor (f :+: g) where
    dimap f g (Inl e) = Inl (dimap f g e)
    dimap f g (Inr e) = Inr (dimap f g e)

instance (Ditraversable f m a, Ditraversable g m a)
    => Ditraversable (f :+: g) m a where
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
data (f :*: g) a b = f a b :*: g a b

ffst :: (f :*: g) a b -> f a b
ffst (x :*: _) = x

fsnd :: (f :*: g) a b -> g a b
fsnd (_ :*: x) = x


-- Constant Products
infixr 7 :&:

{-| This data type adds a constant product to a signature. -}
data (f :&: p) a b = f a b :&: p

instance Difunctor f => Difunctor (f :&: p) where
    dimap f g (v :&: c) = dimap f g v :&: c

instance Ditraversable f m a => Ditraversable (f :&: p) m a where
    dimapM f (v :&: c) = liftM (:&: c) (dimapM f v)
    disequence (v :&: c) = liftM (:&: c) (disequence v)

{-| This class defines how to distribute a product over a sum of signatures. -}
class DistProd s p s' | s' -> s, s' -> p where
    {-| Inject a product value over a signature. -}
    injectP :: p -> s a b -> s' a b
    {-| Project a product value from a signature. -}
    projectP :: s' a b -> (s a b, p)

class RemoveP s s' | s -> s'  where
    {-| Remove products from a signature. -}
    removeP :: s a b -> s' a b

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