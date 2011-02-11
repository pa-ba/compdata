{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances, RankNTypes, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Product
-- Copyright   :  3gERP, 2011
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved and Patrick Bahr
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines products on signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Product
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

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Ops
import Data.Comp.Ops
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor

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
constP c = appSigFun (hinjectP c)

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
stripP = appSigFun hremoveP


productTermHom :: (HDistProd f p f', HDistProd g p g', HFunctor g, HFunctor g') 
               => TermHom f g -> TermHom f' g'
productTermHom alg f' = constP p (alg f)
    where (f :&: p) = hprojectP f'





-- | This function is similar to 'project' but applies to signatures
-- with a product which is then ignored.

-- project' :: (HRemoveP s s',s :<<: f) =>
--      NatM Maybe (Cxt h f a) (s' (Cxt h f a))
project' v = liftM hremoveP $ project v