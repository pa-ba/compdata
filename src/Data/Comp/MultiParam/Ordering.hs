{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
  UndecidableInstances, IncoherentInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Ordering
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines ordering of signatures, which lifts to ordering of
-- terms and contexts.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam.Ordering
    (
     POrd(..),
     OrdHD(..)
    ) where

import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.Sum
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.FreshM
import Data.Comp.MultiParam.Equality

-- |Ordering of parametric values.
class PEq a => POrd a where
    pcompare :: a i -> a j -> FreshM Ordering

instance Ord a => POrd (K a) where
    pcompare (K x) (K y) = return $ compare x y

{-| Signature ordering. An instance @OrdHD f@ gives rise to an instance
  @Ord (Term f)@. -}
class EqHD f => OrdHD f where
    compareHD :: POrd a => f Var a i -> f Var a j -> FreshM Ordering

{-| Ordering on functions means ordering on the codomain. -}
instance OrdHD (:~>) where
    compareHD ((:~>) f) ((:~>) g) =
        do x <- genVar
           pcompare (f $ varCoerce x) (g $ varCoerce x)

{-| 'OrdHD' is propagated through sums. -}
instance (OrdHD f, OrdHD g) => OrdHD (f :+: g) where
    compareHD (Inl x) (Inl y) = compareHD x y
    compareHD (Inl _) (Inr _) = return LT
    compareHD (Inr x) (Inr y) = compareHD x y
    compareHD (Inr _) (Inl _) = return GT

{-| From an 'OrdHD' difunctor an 'Ord' instance of the corresponding term type
  can be derived. -}
instance OrdHD f => OrdHD (Cxt h f) where
    compareHD (Term e1) (Term e2) = compareHD e1 e2
    compareHD (Hole h1) (Hole h2) = pcompare h1 h2
    compareHD (Place p1) (Place p2) = pcompare p1 p2
    compareHD (Term _) _ = return LT
    compareHD (Hole _) (Term _) = return GT
    compareHD (Hole _) (Place _) = return LT
    compareHD (Place _) _ = return GT

instance POrd Var where
    pcompare x y = return $ varCompare x y

instance (OrdHD f, POrd a) => POrd (Cxt h f Var a) where
    pcompare = compareHD

{-| Ordering of terms. -}
instance (HDifunctor f, OrdHD f) => Ord (Term f i) where
    compare x y = evalFreshM $ compareHD (coerceCxt x) (coerceCxt y)