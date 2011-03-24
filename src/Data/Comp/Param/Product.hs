{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Product
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines products on signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Product
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

import Data.Comp.Param.Functor
import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Algebra

import Control.Monad



{-| Transform a function with a domain constructed from a functor to a function
 with a domain constructed with the same functor, but with an additional
 product. -}

liftP :: (RemoveP s s') => (s' a b -> t) -> s a b -> t
liftP f v = f (removeP v)


{-| Transform a function with a domain constructed from a functor to a function
  with a domain constructed with the same functor, but with an additional
  product. -}
liftP' :: (DistProd s' p s, Difunctor s, Difunctor s')
       => (s' a b -> Cxt s' c c) -> s a b -> Cxt s c c
liftP' f v = let (v',p) = projectP v
             in constP p (f v')

{-| Strip the products from a term over a functor with products. -}
stripP :: (Difunctor f, RemoveP g f, Difunctor g) => CxtFun g f
stripP = appSigFun removeP

{-| Lift a term homomorphism over signatures @f@ and @g@ to a term homomorphism
 over the same signatures, but extended with products. -}
productTermHom :: (DistProd f p f', DistProd g p g', Difunctor g, Difunctor g') 
               => TermHom f g -> TermHom f' g'
productTermHom alg f' = constP p (alg f)
    where (f,p) = projectP f'

{-| Annotate each node of a term with a constant value. -}
constP :: forall f g p a b. (DistProd f p g, Difunctor f)
       => p -> Cxt f a b -> Cxt g a b
constP c = run --appSigFun (injectP c)
    where run :: Cxt f a b -> Cxt g a b
          run (Hole x) = Hole x
          run (Term t) = Term $ injectP c $ fmap run t

{-| This function is similar to 'project' but applies to signatures
with a product which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (RemoveP f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM removeP $ project v