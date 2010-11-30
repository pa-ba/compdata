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
      compList
    ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Sum
import Data.ALaCarte.Equality ()
import Data.ALaCarte.Derive
import Data.ALaCarte.Derive.Utils


instance (OrdF f, Ord a) => Ord (Cxt h f a) where
    compare = compareF

{-|
  From an 'OrdF' functor an 'Ord' instance of the corresponding
  term type can be derived.
-}
instance (OrdF f) => OrdF (Cxt h f) where
    compareF (Term e1) (Term e2) = compareF e1 e2
    compareF (Hole h1) (Hole h2) = compare h1 h2
    compareF Term{} Hole{} = LT
    compareF Hole{} Term{} = GT

-- instance (OrdF f, Ord p) => OrdF (f :*: p) where
--     compareF (v1 :*: p1) (v2 :*: p2) = 
--         case compareF v1 v2 of
--           EQ ->  compare p1 p2
--           res -> res

{-|
  'OrdF' is propagated through sums.
-}

instance (OrdF f, OrdF g) => OrdF (f :+: g) where
    compareF (Inl _) (Inr _) = LT
    compareF (Inr _) (Inl _) = GT
    compareF (Inl x) (Inl y) = compareF x y
    compareF (Inr x) (Inr y) = compareF x y

$(derive [instanceOrdF] $ [''Maybe, ''[]] ++ tupleTypes 2 10)