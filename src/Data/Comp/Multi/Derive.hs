--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Derive
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module contains functionality for automatically deriving boilerplate
-- code using Template Haskell. Examples include instances of 'HFunctor',
-- 'HFoldable', and 'HTraversable'.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Derive
    (
     derive,
     -- |Derive boilerplate instances for higher-order signatures, i.e.
     -- signatures for generalised compositional data types.

     -- ** HShowF
     module Data.Comp.Multi.Derive.Show,
     -- ** EqHF
     module Data.Comp.Multi.Derive.Equality,
     -- ** OrdHF
     module Data.Comp.Multi.Derive.Ordering,
     -- ** HFunctor
     module Data.Comp.Multi.Derive.Functor,
     -- ** HFoldable
     module Data.Comp.Multi.Derive.Foldable,
     -- ** HTraversable
     module Data.Comp.Multi.Derive.Traversable,
     -- ** Smart Constructors
     module Data.Comp.Multi.Derive.SmartConstructors,
     -- ** Smart Constructors w/ Annotations
     module Data.Comp.Multi.Derive.SmartAConstructors,
     -- ** Lifting to Sums
     module Data.Comp.Multi.Derive.LiftSum
    ) where

import Data.Comp.Derive.Utils (derive)
import Data.Comp.Multi.Derive.Equality
import Data.Comp.Multi.Derive.Ordering
import Data.Comp.Multi.Derive.Show
import Data.Comp.Multi.Derive.Functor
import Data.Comp.Multi.Derive.Foldable
import Data.Comp.Multi.Derive.Traversable
import Data.Comp.Multi.Derive.SmartConstructors
import Data.Comp.Multi.Derive.SmartAConstructors
import Data.Comp.Multi.Derive.LiftSum