{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Annotation
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines annotations on signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Annotation
    (
     (:&:) (..),
     (:*:) (..),
     DistAnn (..),
     RemA (..),
     liftA,
     liftA',
     stripA,
     propAnn,
     propAnnM,
     ann,
     project'
    ) where

import qualified Data.Comp.Ops as O
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.Sum
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.Algebra

import Control.Monad

{-| Transform a function with a domain constructed from a functor to a function
 with a domain constructed with the same functor, but with an additional
 annotation. -}
liftA :: (RemA s s') => (s' a b :-> t) -> s a b :-> t
liftA f v = f (remA v)

{-| Transform a function with a domain constructed from a functor to a function
  with a domain constructed with the same functor, but with an additional
  annotation. -}
liftA' :: (DistAnn s' p s, HDifunctor s, HDifunctor s')
          => (s' a b :-> Cxt h s' c d) -> s a b :-> Cxt h s c d
liftA' f v = let v' O.:&: p = projectA v
             in ann p (f v')

{-| Strip the annotations from a term over a functor with annotations. -}
stripA :: (HDifunctor f, RemA g f, HDifunctor g) => CxtFun g f
stripA = appSigFun remA

{-| Lift a term homomorphism over signatures @f@ and @g@ to a term homomorphism
 over the same signatures, but extended with annotations. -}
propAnn :: (DistAnn f p f', DistAnn g p g', HDifunctor g, HDifunctor g') 
               => TermHom f g -> TermHom f' g'
propAnn alg f' = ann p (alg f)
    where f O.:&: p = projectA f'

{-| Lift a monadic term homomorphism over signatures @f@ and @g@ to a monadic
  term homomorphism over the same signatures, but extended with annotations. -}
propAnnM :: (DistAnn f p f', DistAnn g p g', HDifunctor g, HDifunctor g',
             Monad m) => TermHomM m f g a -> TermHomM m f' g' a
propAnnM alg f' = liftM (ann p) (alg f)
    where f O.:&: p = projectA f'

{-| Annotate each node of a term with a constant value. -}
ann :: forall h f g p a b. (DistAnn f p g, HDifunctor f, HDifunctor g)
       => p -> Cxt h f a b :-> Cxt h g a b
ann c = appSigFun (injectA c)

{-| This function is similar to 'project' but applies to signatures
with an annotation which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (RemA f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM remA $ project v