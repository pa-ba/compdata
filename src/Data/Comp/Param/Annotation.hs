{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, RankNTypes, GADTs, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Annotation
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines annotations on signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Annotation
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

import Data.Comp.Param.Difunctor
import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Algebra

import Control.Monad



{-| Transform a function with a domain constructed from a functor to a function
 with a domain constructed with the same functor, but with an additional
 annotation. -}

liftA :: (RemA s s') => (s' a b -> t) -> s a b -> t
liftA f v = f (remA v)


{-| Transform a function with a domain constructed from a functor to a function
  with a domain constructed with the same functor, but with an additional
  annotation. -}
liftA' :: (DistAnn s' p s, Difunctor s, Difunctor s')
       => (s' a b -> Cxt s' c c) -> s a b -> Cxt s c c
liftA' f v = let (v',p) = projectA v
             in ann p (f v')

{-| Strip the annotations from a term over a functor with annotations. -}
stripA :: (Difunctor f, RemA g f, Difunctor g) => CxtFun g f
stripA = appSigFun remA

{-| Lift a term homomorphism over signatures @f@ and @g@ to a term homomorphism
 over the same signatures, but extended with annotations. -}
propAnn :: (DistAnn f p f', DistAnn g p g', Difunctor g, Difunctor g') 
               => TermHom f g -> TermHom f' g'
propAnn alg f' = ann p (alg f)
    where (f,p) = projectA f'

{-| Lift a monadic term homomorphism over signatures @f@ and @g@ to a monadic
  term homomorphism over the same signatures, but extended with annotations. -}
propAnnM :: (DistAnn f p f', DistAnn g p g',
                    Difunctor g, Difunctor g', Monad m) 
               => TermHomM m f g a -> TermHomM m f' g' a
propAnnM alg f' = liftM (ann p) (alg f)
    where (f,p) = projectA f'

{-| Annotate each node of a term with a constant value. -}
ann :: forall f g p a b. (DistAnn f p g, Difunctor f, Difunctor g, a :< b)
       => p -> Cxt f a b -> Cxt g a b
ann c = appSigFun (injectA c)

{-| This function is similar to 'project' but applies to signatures
with an annotation which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (RemA f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM remA $ project v