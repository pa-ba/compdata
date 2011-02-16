{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, RankNTypes, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Product
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines products on signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Product
    ( (:&:) (..),
      (:*:) (..),
      DistProd (..),
      RemoveP (..),
      liftP,
      liftP',
      stripP,
      productTermHom,
      constP,
      project'
    )where

import Data.Comp.Term
import Data.Comp.Sum
import Data.Comp.Ops
import Data.Comp.Algebra

import Control.Monad



{-| Transform a function with a domain constructed from a functor to a function
 with a domain constructed with the same functor, but with an additional
 product. -}

liftP :: (RemoveP s s') => (s' a -> t) -> s a -> t
liftP f v = f (removeP v)


{-| Transform a function with a domain constructed from a functor to a function
  with a domain constructed with the same functor, but with an additional
  product. -}
liftP' :: (DistProd s' p s, Functor s, Functor s')
       => (s' a -> Cxt h s' a) -> s a -> Cxt h s a
liftP' f v = let (v',p) = projectP v
             in constP p (f v')
    
{-| Strip the products from a term over a functor with products. -}
stripP :: (Functor f, RemoveP g f, Functor g) => Cxt h g a -> Cxt h f a
stripP = appSigFun removeP

{-| Lift a term homomorphism over signatures @f@ and @g@ to a term homomorphism
 over the same signatures, but extended with products. -}
productTermHom :: (DistProd f p f', DistProd g p g', Functor g, Functor g') 
            => TermHom f g -> TermHom f' g'
productTermHom alg f' = constP p (alg f)
    where (f,p) = projectP f'

{-| Annotate each node of a term with a constant value. -}
constP :: (DistProd f p g, Functor f, Functor g) 
       => p -> Cxt h f a -> Cxt h g a
constP c = appSigFun (injectP c)

{-| This function is similar to 'project' but applies to signatures
with a product which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (RemoveP f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM removeP $ project v