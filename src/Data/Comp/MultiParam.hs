--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>, Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use
-- /Generalised Parametric Compositional Data Types/. Generalised Parametric
-- Compositional Data Types is an extension of Compositional Data Types with
-- parametric higher-order abstract syntax (PHOAS) for usage with binders, and
-- GADTs. Generalised Parametric Compositional Data Types combines Generalised
-- Compositional Data Types ("Data.Comp.Multi") and Parametric Compositional
-- Data Types ("Data.Comp.Param"). Examples of usage are bundled with the
-- package in the library @examples\/Examples\/MultiParam@.
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