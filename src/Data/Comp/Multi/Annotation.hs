{-# LANGUAGE TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, UndecidableInstances, RankNTypes, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Annotation
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines annotations on signatures. All definitions are
-- generalised versions of those in "Data.Comp.Annotation".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Annotation
    (
     (:&:) (..),
     DistAnn (..),
     RemA (..),
     liftA,
     ann,
     liftA',
     stripA,
     propAnn,
     project'
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Ops
import qualified Data.Comp.Ops as O
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Functor

import Control.Monad

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional annotation.
liftA :: (RemA s s') => (s' a :-> t) -> s a :-> t
liftA f v = f (remA v)


-- | This function annotates each sub term of the given term with the
-- given value (of type a).

ann :: (DistAnn f p g, HFunctor f) => p -> CxtFun f g
ann c = appSigFun (injectA c)

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional annotation.
liftA' :: (DistAnn s' p s, HFunctor s')
       => (s' a :-> Cxt h s' a) -> s a :-> Cxt h s a
liftA' f v = let (v' O.:&: p) = projectA v
             in ann p (f v')
    
{-| This function strips the annotations from a term over a
functor with annotations. -}

stripA :: (RemA g f, HFunctor g) => CxtFun g f
stripA = appSigFun remA


propAnn :: (DistAnn f p f', DistAnn g p g', HFunctor g) 
               => Hom f g -> Hom f' g'
propAnn alg f' = ann p (alg f)
    where (f O.:&: p) = projectA f'

-- | This function is similar to 'project' but applies to signatures
-- with an annotation which is then ignored.

-- project' :: (RemA s s',s :<: f) =>
--      NatM Maybe (Cxt h f a) (s' (Cxt h f a))
project' v = liftM remA $ project v