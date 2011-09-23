--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>, Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use
-- /Compositional Data Types/. Compositional Data Types is an extension of
-- Wouter Swierstra's Functional Pearl: /Data types a la carte/. Examples of
-- usage are bundled with the package in the library @examples\/Examples@.
--
--------------------------------------------------------------------------------
module Data.Comp
    (
     module X
    ) where

import Data.Comp.Term as X
import Data.Comp.Algebra as X
import Data.Comp.Sum as X
import Data.Comp.Annotation as X
import Data.Comp.Equality as X
import Data.Comp.Ordering as X
import Data.Comp.Generic as X