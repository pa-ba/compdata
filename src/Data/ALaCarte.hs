{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             UndecidableInstances, FlexibleInstances, FlexibleContexts,
             ScopedTypeVariables, FunctionalDependencies, EmptyDataDecls,
             GADTs, KindSignatures, RankNTypes, TypeSynonymInstances, TypeFamilies#-}
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
    ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Algebra
import Data.ALaCarte.Sum
import Data.ALaCarte.Product
