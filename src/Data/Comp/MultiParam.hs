--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use parametric
-- compositional data types.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam (
    module Data.Comp.MultiParam.Term
  , module Data.Comp.MultiParam.Algebra
  , module Data.Comp.MultiParam.HDifunctor
  , module Data.Comp.MultiParam.Sum
  , module Data.Comp.MultiParam.Annotation
  , module Data.Comp.MultiParam.Equality
    ) where

import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.Algebra
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.Sum
import Data.Comp.MultiParam.Annotation
import Data.Comp.MultiParam.Equality