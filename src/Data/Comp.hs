--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use
-- /Compositional Data Types/. Compositional Data Types is an extension of
-- Wouter Swierstra's Functional Pearl: /Data types a la carte/. Examples of
-- usage are bundled with the package in the library @examples\/Examples@.
--
--------------------------------------------------------------------------------
module Data.Comp(
    module Data.Comp.Term
  , module Data.Comp.Algebra
  , module Data.Comp.Sum
  , module Data.Comp.Annotation
  , module Data.Comp.Equality
  , module Data.Comp.Ordering
  , module Data.Comp.Generic
    ) where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Sum
import Data.Comp.Annotation
import Data.Comp.Equality
import Data.Comp.Ordering
import Data.Comp.Generic