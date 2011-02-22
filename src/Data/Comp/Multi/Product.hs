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
    ( (:&&:) (..),
      HDistProd (..),
      HRemoveP (..),
      liftP,
      constP,
      liftP',
      stripP,
      productHTermHom,
      hproject'
    )where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Ops
import Data.Comp.Ops
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Functor

import Control.Monad




-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional product.

liftP :: (HRemoveP s s') => (s' a :-> t) -> s a :-> t
liftP f v = f (hremoveP v)


-- | This function annotates each sub term of the given term with the
-- given value (of type a).

constP :: (HDistProd f p g, HFunctor f, HFunctor g) 
       => p -> HCxt h f a :-> HCxt h g a
constP c = appHSigFun (hinjectP c)

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional product.

liftP' :: (HDistProd s' p s, HFunctor s, HFunctor s')
       => (s' a :-> HCxt h s' a) -> s a :-> HCxt h s a
liftP' f v = let (v' :&: p) = hprojectP v
             in constP p (f v')
    
{-| This function strips the products from a term over a
functor whith products. -}

stripP :: (HFunctor f, HRemoveP g f, HFunctor g)
       => HCxt h g a :-> HCxt h f a
stripP = appHSigFun hremoveP


productHTermHom :: (HDistProd f p f', HDistProd g p g', HFunctor g, HFunctor g') 
               => HTermHom f g -> HTermHom f' g'
productHTermHom alg f' = constP p (alg f)
    where (f :&: p) = hprojectP f'





-- | This function is similar to 'hproject' but applies to signatures
-- with a product which is then ignored.

-- hproject' :: (HRemoveP s s',s :<<: f) =>
--      NatM Maybe (HCxt h f a) (s' (HCxt h f a))
hproject' v = liftM hremoveP $ hproject v