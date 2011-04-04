{-# LANGUAGE TypeOperators, GADTs, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Equality
-- Copyright   :  (c) Patrick Bahr, 2011
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines equality for (higher-order) signatures, which lifts to
-- equality for (higher-order) terms and contexts. All definitions are
-- generalised versions of those in "Data.Comp.Equality".
--
--------------------------------------------------------------------------------
module Data.Comp.Multi.Equality
    (
     HEqF(..),
     KEq(..),
     heqMod
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Derive

import Data.Comp.Multi.Functor
import Data.Comp.Multi.Foldable

{-|
  'EqF' is propagated through sums.
-}

instance (HEqF f, HEqF g) => HEqF (f :+: g) where
    heqF (Inl x) (Inl y) = heqF x y
    heqF (Inr x) (Inr y) = heqF x y
    heqF _ _ = False

{-|
  From an 'EqF' functor an 'Eq' instance of the corresponding
  term type can be derived.
-}
instance (HEqF f) => HEqF (Cxt h f) where

    heqF (Term e1) (Term e2) = e1 `heqF` e2
    heqF (Hole h1) (Hole h2) = h1 `keq` h2
    heqF _ _ = False

instance (HEqF f, KEq a)  => KEq (Cxt h f a) where
    keq = heqF

instance KEq Nothing where
    keq _ = undefined


{-| This function implements equality of values of type @f a@ modulo
the equality of @a@ itself. If two functorial values are equal in this
sense, 'eqMod' returns a 'Just' value containing a list of pairs
consisting of corresponding components of the two functorial
values. -}

heqMod :: (HEqF f, HFunctor f, HFoldable f) => f a i -> f b i -> Maybe [(A a, A b)]
heqMod s t
    | unit s `heqF` unit' t = Just args
    | otherwise = Nothing
    where unit = hfmap (const $ K ())
          unit' = hfmap (const $ K ())
          args = htoList s `zip` htoList t
