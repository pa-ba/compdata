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

     -- ** Diunctor
     module Data.Comp.Param.Derive.Functor,
{-     -- ** Difoldable
     module Data.Comp.Param.Derive.Foldable,
     -- ** Ditraversable
     module Data.Comp.Param.Derive.Traversable,-}
     -- ** Smart Constructors
     module Data.Comp.Param.Derive.SmartConstructors
    ) where

import Data.Comp.Derive.Utils (derive)
--import Data.Comp.Param.Derive.Equality
--import Data.Comp.Param.Derive.Show
import Data.Comp.Param.Derive.Functor
{-import Data.Comp.Param.Derive.Foldable
import Data.Comp.Param.Derive.Traversable-}
import Data.Comp.Param.Derive.SmartConstructors