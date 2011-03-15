{-# LANGUAGE TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, UndecidableInstances, RankNTypes, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Product
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines products on signatures. All definitions are
-- generalised versions of those in "Data.Comp.Product".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Product
    ( (:&:) (..),
      DistProd (..),
      RemoveP (..),
      liftP,
      constP,
      liftP',
      stripP,
      productTermHom,
      project'
    )where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Ops
import qualified Data.Comp.Ops as O
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Functor

import Control.Monad




-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional product.

liftP :: (RemoveP s s') => (s' a :-> t) -> s a :-> t
liftP f v = f (removeP v)


-- | This function annotates each sub term of the given term with the
-- given value (of type a).

constP :: (DistProd f p g, HFunctor f, HFunctor g) 
       => p -> Cxt h f a :-> Cxt h g a
constP c = appSigFun (injectP c)

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional product.

liftP' :: (DistProd s' p s, HFunctor s, HFunctor s')
       => (s' a :-> Cxt h s' a) -> s a :-> Cxt h s a
liftP' f v = let (v' O.:&: p) = projectP v
             in constP p (f v')
    
{-| This function strips the products from a term over a
functor whith products. -}

stripP :: (HFunctor f, RemoveP g f, HFunctor g)
       => Cxt h g a :-> Cxt h f a
stripP = appSigFun removeP


productTermHom :: (DistProd f p f', DistProd g p g', HFunctor g, HFunctor g') 
               => TermHom f g -> TermHom f' g'
productTermHom alg f' = constP p (alg f)
    where (f O.:&: p) = projectP f'





-- | This function is similar to 'project' but applies to signatures
-- with a product which is then ignored.

-- project' :: (RemoveP s s',s :<: f) =>
--      NatM Maybe (Cxt h f a) (s' (Cxt h f a))
project' v = liftM removeP $ project v