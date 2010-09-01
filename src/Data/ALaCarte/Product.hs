{-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeFamilies, 
             FunctionalDependencies, FlexibleInstances, UndecidableInstances,
             FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Product
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines products on signatures.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Product where

import Data.ALaCarte.Term
import Data.ALaCarte.Sum
import Data.ALaCarte.Algebra

import Data.Foldable
import Data.Traversable

import Control.Monad  hiding (mapM, sequence)
import Control.Applicative

import Prelude hiding (foldl, mapM, sequence, foldl1, foldr1, foldr)


infixr 7 :*:

{-| This data type adds a constant product to a signature.  -}

data (f :*: a) e = f e :*: a


instance (Functor f) => Functor (f :*: a) where
    fmap f (v :*: c) = fmap f v :*: c

instance (Foldable f) => Foldable (f :*: a) where
    fold (v :*: _) = fold v
    foldMap f (v :*: _) = foldMap f v
    foldr f e (v :*: _) = foldr f e v
    foldl f e (v :*: _) = foldl f e v
    foldr1 f (v :*: _) = foldr1 f v
    foldl1 f (v :*: _) = foldl1 f v

instance (Traversable f) => Traversable (f :*: a) where
    traverse f (v :*: c) = liftA (:*: c) (traverse f v)
    sequenceA (v :*: c) = liftA (:*: c)(sequenceA v)
    mapM f (v :*: c) = liftM (:*: c) (mapM f v)
    sequence (v :*: c) = liftM (:*: c) (sequence v)

{-| This class defines how to distribute a product over a sum of
signatures. -}

class DistProd s p s' | s' -> s, s' -> p where
        
    {-| This function injects a product a value over a signature. -}
    injectP :: p -> s a -> s' a
    projectP :: s' a -> (s a, p)


class RemoveP s s' | s -> s'  where
    removeP :: s a -> s' a


instance (RemoveP s s') => RemoveP (f :*: p :+: s) (f :+: s') where
    removeP (Inl (v :*: _)) = Inl v
    removeP (Inr v) = Inr $ removeP v


instance RemoveP (f :*: p) f where
    removeP (v :*: _) = v


instance (DistProd s p s') => DistProd f p (f :*: p) where

    injectP c v = v :*: c

    projectP (v :*: p) = (v,p)


instance (DistProd s p s') => DistProd (f :+: s) p ((f :*: p) :+: s') where


    injectP c (Inl v) = Inl (v :*: c)
    injectP c (Inr v) = Inr $ injectP c v

    projectP (Inl (v :*: p)) = (Inl v,p)
    projectP (Inr v) = let (v',p) = projectP v
                       in  (Inr v',p)


{-| This function transforms a function with a domain constructed from
a functor to a function with a domain constructed with the same
functor but with an additional product. -}

liftP :: (RemoveP s s') => (s' a -> t) -> s a -> t
liftP f v = f (removeP v)
    
{-| This function strips the products from a term over a
functor whith products. -}

stripP :: (Functor f, RemoveP g f, Functor g) => Cxt h g a -> Cxt h f a
stripP = applySigFun removeP



{-| This function annotates each sub term of the given term
with the given value (of type a). -}

constP :: (DistProd f p g, Functor f, Functor g) 
       => p -> Cxt h f a -> Cxt h g a
constP c = applySigFun (injectP c)


{-| This function is similar to 'project' but applies to signatures
with a product which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (RemoveP f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM removeP $ project v
