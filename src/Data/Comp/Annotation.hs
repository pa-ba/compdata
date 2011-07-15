{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, RankNTypes, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Annotation
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines annotations on signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Annotation
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

import Data.Comp.Term
import Data.Comp.Sum
import Data.Comp.Ops
import Data.Comp.Algebra
import Control.Monad

{-| Transform a function with a domain constructed from a functor to a function
 with a domain constructed with the same functor, but with an additional
 annotation. -}
liftA :: (RemA s s') => (s' a -> t) -> s a -> t
liftA f v = f (remA v)

{-| Transform a function with a domain constructed from a functor to a function
  with a domain constructed with the same functor, but with an additional
  annotation. -}
liftA' :: (DistAnn s' p s, Functor s')
       => (s' a -> Cxt h s' a) -> s a -> Cxt h s a
liftA' f v = let (v',p) = projectA v
             in ann p (f v')
    
{-| Strip the annotations from a term over a functor with annotations. -}
stripA :: (RemA g f, Functor g) => CxtFun g f
stripA = appSigFun remA

{-| Lift a term homomorphism over signatures @f@ and @g@ to a term homomorphism
 over the same signatures, but extended with annotations. -}
propAnn :: (DistAnn f p f', DistAnn g p g', Functor g) 
        => Hom f g -> Hom f' g'
propAnn hom f' = ann p (hom f)
    where (f,p) = projectA f'

{-| Lift a monadic term homomorphism over signatures @f@ and @g@ to a monadic
  term homomorphism over the same signatures, but extended with annotations. -}
propAnnM :: (DistAnn f p f', DistAnn g p g', Functor g, Monad m) 
         => HomM m f g -> HomM m f' g'
propAnnM hom f' = liftM (ann p) (hom f)
    where (f,p) = projectA f'

{-| Annotate each node of a term with a constant value. -}
ann :: (DistAnn f p g, Functor f) => p -> CxtFun f g
ann c = appSigFun (injectA c)

{-| This function is similar to 'project' but applies to signatures
with an annotation which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (RemA f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM remA $ project v