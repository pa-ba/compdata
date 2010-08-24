{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Ordering
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- The ordering algebra (orderings on terms).
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Ordering
    ( OrdF(..),
      compList,
      deriveOrdFs,
      deriveOrdF
    ) where

import Data.ALaCarte
import Data.ALaCarte.Derive.Ordering
import Data.ALaCarte.Derive.Utils


instance (OrdF f, Ord a) => Ord (Cxt h f a) where
    compare = compAlg

{-|
  From an 'OrdF' functor an 'Ord' instance of the corresponding
  term type can be derived.
-}
instance (OrdF f) => OrdF (Cxt h f) where
    compAlg (Term e1) (Term e2) = compAlg e1 e2
    compAlg (Hole h1) (Hole h2) = compare h1 h2
    compAlg Term{} Hole{} = LT
    compAlg Hole{} Term{} = GT

{-|
  'OrdF' is propagated through sums.
-}

instance (OrdF f, OrdF g) => OrdF (f :+: g) where
    compAlg (Inl _) (Inr _) = LT
    compAlg (Inr _) (Inl _) = GT
    compAlg (Inl x) (Inl y) = compAlg x y
    compAlg (Inr x) (Inr y) = compAlg x y

$(deriveOrdFs $ [''Maybe, ''[]] ++ tupleTypes 2 10)