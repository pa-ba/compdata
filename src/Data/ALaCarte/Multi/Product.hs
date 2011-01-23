{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances, RankNTypes, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Multi.Product
-- Copyright   :  3gERP, 2011
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved and Patrick Bahr
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines products on signatures.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Multi.Product
    ( (:&&:) (..),
      HDistProd (..),
      HRemoveP (..),
      liftP,
      constP,
      liftP',
      stripP,
      productTermHom,
      project'
    )where

import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.Sum
import Data.ALaCarte.Multi.Ops
import Data.ALaCarte.Ops
import Data.ALaCarte.Multi.Algebra
import Data.ALaCarte.Multi.HFunctor

import Control.Monad




-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional product.

liftP :: (HRemoveP s s') => (s' a :-> t) -> s a :-> t
liftP f v = f (hremoveP v)


-- | This function annotates each sub term of the given term with the
-- given value (of type a).

constP :: (HDistProd f p g, HFunctor f, HFunctor g) 
       => p -> Cxt h f a :-> Cxt h g a
constP c = applySigFun (hinjectP c)

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional product.

liftP' :: (HDistProd s' p s, HFunctor s, HFunctor s')
       => (s' a :-> Cxt h s' a) -> s a :-> Cxt h s a
liftP' f v = let (v' :&: p) = hprojectP v
             in constP p (f v')
    
{-| This function strips the products from a term over a
functor whith products. -}

stripP :: (HFunctor f, HRemoveP g f, HFunctor g)
       => Cxt h g a :-> Cxt h f a
stripP = applySigFun hremoveP


productTermHom :: (HDistProd f p f', HDistProd g p g', HFunctor g, HFunctor g') 
               => TermHom f g -> TermHom f' g'
productTermHom alg f' = constP p (alg f)
    where (f :&: p) = hprojectP f'





-- | This function is similar to 'project' but applies to signatures
-- with a product which is then ignored.

-- project' :: (HRemoveP s s',s :<<: f) =>
--      NatM Maybe (Cxt h f a) (s' (Cxt h f a))
project' v = liftM hremoveP $ project v