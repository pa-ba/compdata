{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, UndecidableInstances, IncoherentInstances,
  KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Ops
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Ops where

import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.HDitraversable
import qualified Data.Comp.Ops as O
import Control.Monad (liftM)


-- Sums
infixr 6 :+:

-- |Formal sum of signatures (difunctors).
data (f :+: g) (a :: * -> *) (b :: * -> *) i = Inl (f a b i)
                                             | Inr (g a b i)

instance (HDifunctor f, HDifunctor g) => HDifunctor (f :+: g) where
    dimap f g (Inl e) = Inl (dimap f g e)
    dimap f g (Inr e) = Inr (dimap f g e)

instance (HDitraversable f m a, HDitraversable g m a)
    => HDitraversable (f :+: g) m a where
    dimapM f (Inl e) = Inl `liftM` dimapM f e
    dimapM f (Inr e) = Inr `liftM` dimapM f e
--    disequence (Inl e) = Inl `liftM` disequence e
--    disequence (Inr e) = Inr `liftM` disequence e

-- | Signature containment relation for automatic injections. The left-hand must
-- be an atomic signature, where as the right-hand side must have a list-like
-- structure. Examples include @f :<: f :+: g@ and @g :<: f :+: (g :+: h)@,
-- non-examples include @f :+: g :<: f :+: (g :+: h)@ and
-- @f :<: (f :+: g) :+: h@.
class (sub :: (* -> *) -> (* -> *) -> * -> *) :<: sup where
    inj :: sub a b :-> sup a b
    proj :: NatM Maybe (sup a b) (sub a b)

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
data (f :&: p) (a :: * -> *) (b :: * -> *) i = f a b i :&: p

instance HDifunctor f => HDifunctor (f :&: p) where
    dimap f g (v :&: c) = dimap f g v :&: c

instance HDitraversable f m a => HDitraversable (f :&: p) m a where
    dimapM f (v :&: c) = liftM (:&: c) (dimapM f v)
--    disequence (v :&: c) = liftM (:&: c) (disequence v)

{-| This class defines how to distribute an annotation over a sum of
  signatures. -}
class DistAnn (s :: (* -> *) -> (* -> *) -> * -> *) p s' | s' -> s, s' -> p where
    {-| Inject an annotation over a signature. -}
    injectA :: p -> s a b :-> s' a b
    {-| Project an annotation from a signature. -}
    projectA :: s' a b :-> (s a b O.:&: p)

class RemA (s :: (* -> *) -> (* -> *) -> * -> *) s' | s -> s' where
    {-| Remove annotations from a signature. -}
    remA :: s a b :-> s' a b

instance (RemA s s') => RemA (f :&: p :+: s) (f :+: s') where
    remA (Inl (v :&: _)) = Inl v
    remA (Inr v) = Inr $ remA v

instance RemA (f :&: p) f where
    remA (v :&: _) = v

instance DistAnn f p (f :&: p) where
    injectA c v = v :&: c

    projectA (v :&: p) = v O.:&: p

instance (DistAnn s p s') => DistAnn (f :+: s) p ((f :&: p) :+: s') where
    injectA c (Inl v) = Inl (v :&: c)
    injectA c (Inr v) = Inr $ injectA c v

    projectA (Inl (v :&: p)) = Inl v O.:&: p
    projectA (Inr v) = let (v' O.:&: p) = projectA v
                       in Inr v' O.:&: p