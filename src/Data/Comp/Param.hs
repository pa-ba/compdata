--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use parametric
-- compositional data types. Examples of usage are provided below.
--
--------------------------------------------------------------------------------
module Data.Comp.Param (
  -- * Examples
    module Data.Comp.Param.Term
  , module Data.Comp.Param.Algebra
  , module Data.Comp.Param.Functor
  , module Data.Comp.Param.Sum
  , module Data.Comp.Param.Product
  , module Data.Comp.Param.Equality
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Algebra
import Data.Comp.Param.Functor
import Data.Comp.Param.Sum
import Data.Comp.Param.Product
import Data.Comp.Param.Equality