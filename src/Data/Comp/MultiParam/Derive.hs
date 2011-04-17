--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module contains functionality for automatically deriving boilerplate
-- code using Template Haskell. Examples include instances of 'HDifunctor',
-- 'Difoldable', and 'HDitraversable'.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Derive
    (
     derive,
     -- |Derive boilerplate instances for parametric signatures, i.e.
     -- signatures for parametric compositional data types.

     -- ** EqD
     module Data.Comp.MultiParam.Derive.Equality,
     -- ** OrdD
     module Data.Comp.MultiParam.Derive.Ordering,
     -- ** ShowD
     module Data.Comp.MultiParam.Derive.Show,
     -- ** HDifunctor
     module Data.Comp.MultiParam.Derive.HDifunctor,
     -- ** Foldable
     module Data.Comp.Multi.Derive.Foldable,
     -- ** Traversable
     module Data.Comp.Multi.Derive.Traversable,
     -- ** Smart Constructors
     module Data.Comp.MultiParam.Derive.SmartConstructors,
     -- ** Smart Constructors w/ Annotations
     module Data.Comp.MultiParam.Derive.SmartAConstructors,
     -- ** Lifting to Sums
     module Data.Comp.MultiParam.Derive.LiftSum
    ) where

import Data.Comp.Derive.Utils (derive)
import Data.Comp.MultiParam.Derive.Equality
import Data.Comp.MultiParam.Derive.Ordering
import Data.Comp.MultiParam.Derive.Show
import Data.Comp.MultiParam.Derive.HDifunctor
import Data.Comp.Multi.Derive.Foldable
import Data.Comp.Multi.Derive.Traversable
import Data.Comp.MultiParam.Derive.SmartConstructors
import Data.Comp.MultiParam.Derive.SmartAConstructors
import Data.Comp.MultiParam.Derive.LiftSum