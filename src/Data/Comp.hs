--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines the infrastructure necessary to use Wouter Swierstra's
-- Functional Pearl: /Data types a la carte/.
--
--------------------------------------------------------------------------------
module Data.Comp(
    module Data.Comp.Term
  , module Data.Comp.Algebra
  , module Data.Comp.Sum
  , module Data.Comp.Product
  , module Data.Comp.Equality
  , module Data.Comp.Ordering
  , module Data.Comp.Generic
    ) where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Sum
import Data.Comp.Product
import Data.Comp.Equality
import Data.Comp.Ordering
import Data.Comp.Generic