--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte
-- Copyright   :  3gERP, 2011
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines the infrastructure necessary to use data types
-- a la carte for mutually recursive data types.
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Multi (
    module Data.ALaCarte.Multi.Term
  , module Data.ALaCarte.Multi.Algebra
  , module Data.ALaCarte.Multi.HFunctor
  , module Data.ALaCarte.Multi.Sum
  , module Data.ALaCarte.Multi.Product
    ) where

import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.Algebra
import Data.ALaCarte.Multi.HFunctor
import Data.ALaCarte.Multi.Sum
import Data.ALaCarte.Multi.Product