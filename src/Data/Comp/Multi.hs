--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp
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
module Data.Comp.Multi (
    module Data.Comp.Multi.Term
  , module Data.Comp.Multi.Algebra
  , module Data.Comp.Multi.HFunctor
  , module Data.Comp.Multi.Sum
  , module Data.Comp.Multi.Product
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Product