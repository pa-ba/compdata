{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
  UndecidableInstances, IncoherentInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ordering
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
module Data.Comp.Param.Ordering
    (
     POrd(..),
     OrdD(..)
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.FreshM
import Data.Comp.Param.Equality

-- |Ordering of parametric values.
class PEq a => POrd a where
    pcompare :: a -> a -> FreshM Ordering

instance Ord a => POrd a where
    pcompare x y = return $ compare x y

{-| Signature ordering. An instance @OrdD f@ gives rise to an instance
  @Ord (Term f)@. -}
class EqD f => OrdD f where
    compareD :: POrd a => f Var a -> f Var a -> FreshM Ordering

{-| Ordering on functions means ordering on the codomain. -}
instance OrdD (->) where
    compareD f g = do x <- genVar
                      pcompare (f x) (g x)

{-| 'OrdD' is propagated through sums. -}
instance (OrdD f, OrdD g) => OrdD (f :+: g) where
    compareD (Inl x) (Inl y) = compareD x y
    compareD (Inl _) (Inr _) = return LT
    compareD (Inr x) (Inr y) = compareD x y
    compareD (Inr _) (Inl _) = return GT

{-| From an 'OrdD' difunctor an 'Ord' instance of the corresponding term type
  can be derived. -}
instance OrdD f => OrdD (Cxt h f) where
    compareD (Term e1) (Term e2) = compareD e1 e2
    compareD (Hole h1) (Hole h2) = pcompare h1 h2
    compareD (Place p1) (Place p2) = pcompare p1 p2
    compareD (Term _) _ = return LT
    compareD (Hole _) (Term _) = return GT
    compareD (Hole _) (Place _) = return LT
    compareD (Place _) _ = return GT

instance (OrdD f, POrd a) => POrd (Cxt h f Var a) where
    pcompare = compareD

{-| Ordering of terms. -}
instance (Difunctor f, OrdD f) => Ord (Term f) where
    compare x y = evalFreshM $ compareD (coerceCxt x) (coerceCxt y)