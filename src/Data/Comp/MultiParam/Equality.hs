{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
  UndecidableInstances, IncoherentInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Equality
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines equality for signatures, which lifts to equality for
-- terms.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam.Equality
    (
     PEq(..),
     EqHD(..)
    ) where

import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.Sum
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.FreshM

-- |Equality on parametric values. The equality test is performed inside the
-- 'FreshM' monad for generating fresh identifiers.
class PEq a where
    peq :: a i -> a j -> FreshM Bool

instance Eq a => PEq (K a) where
    peq (K x) (K y) = return $ x == y

{-| Signature equality. An instance @EqHD f@ gives rise to an instance
  @Eq (Term f i)@. The equality test is performed inside the 'FreshM' monad for
  generating fresh identifiers. -}
class EqHD f where
    eqHD :: PEq a => f Var a i -> f Var a j -> FreshM Bool

{-| 'EqHD' is propagated through sums. -}
instance (EqHD f, EqHD g) => EqHD (f :+: g) where
    eqHD (Inl x) (Inl y) = eqHD x y
    eqHD (Inr x) (Inr y) = eqHD x y
    eqHD _ _ = return False

instance PEq Var where
   peq x y = return $ (varCoerce x) == y

{-| From an 'EqHD' difunctor an 'Eq' instance of the corresponding term type can
  be derived. -}
instance EqHD f => EqHD (Cxt h f) where
    eqHD (Term e1) (Term e2) = eqHD e1 e2
    eqHD (Hole h1) (Hole h2) = peq h1 h2
    eqHD (Place p1) (Place p2) = peq p1 p2
    eqHD _ _ = return False

instance (EqHD f, PEq a) => PEq (Cxt h f Var a) where
    peq = eqHD

{-| Equality on terms. -}
instance (HDifunctor f, EqHD f) => Eq (Term f i) where
    (==) x y = evalFreshM $ eqHD (coerceCxt x) (coerceCxt y)