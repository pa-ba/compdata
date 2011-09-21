{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Ordering
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines ordering of signatures, which lifts to ordering of
-- terms and contexts.
--
--------------------------------------------------------------------------------
module Data.Comp.Ordering
    (
     OrdF(..)
    ) where

import Data.Comp.Term
import Data.Comp.Sum
import Data.Comp.Ops
import Data.Comp.Equality ()
import Data.Comp.Derive
import Data.Comp.Derive.Utils

{-|
  From an 'OrdF' functor an 'Ord' instance of the corresponding
  term type can be derived.
-}
instance (OrdF f, Ord a) => Ord (Cxt h f a) where
    compare = compareF

instance OrdF f => OrdF (Cxt h f) where
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

$(derive [makeOrdF] $ [''Maybe, ''[]] ++ tupleTypes 2 10)