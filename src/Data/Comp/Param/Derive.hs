--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module contains functionality for automatically deriving boilerplate
-- code using Template Haskell. Examples include instances of 'Difunctor',
-- 'Difoldable', and 'Ditraversable'.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive
    (
     derive,
     -- |Derive boilerplate instances for parametric signatures, i.e.
     -- signatures for parametric compositional data types.

     -- ** EqD
     module Data.Comp.Param.Derive.Equality,
     -- ** OrdD
     module Data.Comp.Param.Derive.Ordering,
     -- ** ShowD
     module Data.Comp.Param.Derive.Show,
     -- ** Difunctor
     module Data.Comp.Param.Derive.Functor,
     -- ** Foldable
     module Data.Comp.Derive.Foldable,
     -- ** Traversable
     module Data.Comp.Derive.Traversable,
     -- ** Smart Constructors
     module Data.Comp.Param.Derive.SmartConstructors
    ) where

import Data.Comp.Derive.Utils (derive)
import Data.Comp.Param.Derive.Equality
import Data.Comp.Param.Derive.Ordering
import Data.Comp.Param.Derive.Show
import Data.Comp.Param.Derive.Functor
import Data.Comp.Derive.Foldable
import Data.Comp.Derive.Traversable
import Data.Comp.Param.Derive.SmartConstructors