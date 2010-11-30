--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte
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
module Data.ALaCarte(
    module Data.ALaCarte.Term
  , module Data.ALaCarte.Algebra
  , module Data.ALaCarte.Sum
  , module Data.ALaCarte.Product
  , module Data.ALaCarte.Equality
  , module Data.ALaCarte.Ordering
    ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Algebra
import Data.ALaCarte.Sum
import Data.ALaCarte.Product
import Data.ALaCarte.Equality
import Data.ALaCarte.Ordering