--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Derive (
  module Data.ALaCarte.Derive.Show,
  module Data.ALaCarte.Derive.Ordering,
  module Data.ALaCarte.Derive.Equality,
  module Data.ALaCarte.Derive.Arbitrary,
  module Data.ALaCarte.Derive.SmartConstructors,
  module Data.ALaCarte.Derive.SmartMConstructors,
  module Data.ALaCarte.Derive.DeepSeq,
  module Data.ALaCarte.Derive.Foldable,
  module Data.ALaCarte.Derive.Traversable,
  module Data.ALaCarte.Derive.HFunctor,
  module Data.ALaCarte.Derive.HFoldable,
  module Data.ALaCarte.Derive.HTraversable,
  module Data.ALaCarte.Derive.HShow,
  module Data.ALaCarte.Derive.HEquality,
  module Control.DeepSeq,
  instanceFunctor,
  instanceNFData,
  derive ) where


import Control.DeepSeq
import Data.ALaCarte.Derive.HEquality
import Data.ALaCarte.Derive.HShow
import Data.ALaCarte.Derive.HFunctor
import Data.ALaCarte.Derive.HFoldable
import Data.ALaCarte.Derive.HTraversable
import Data.ALaCarte.Derive.Foldable
import Data.ALaCarte.Derive.Traversable
import Data.ALaCarte.Derive.DeepSeq
import Data.ALaCarte.Derive.Show
import Data.ALaCarte.Derive.Ordering
import Data.ALaCarte.Derive.Equality
import Data.ALaCarte.Derive.Arbitrary
import Data.ALaCarte.Derive.SmartConstructors
import Data.ALaCarte.Derive.SmartMConstructors

import Language.Haskell.TH
import Control.Monad

import qualified Data.DeriveTH as D
import Data.Derive.All

derive :: [Name -> Q [Dec]] -> [Name] -> Q [Dec]
derive ders names = liftM concat $ sequence [der name | der <- ders, name <- names]

instanceFunctor :: Name -> Q [Dec]
instanceFunctor = D.derive makeFunctor

instanceNFData :: Name -> Q [Dec]
instanceNFData = D.derive makeNFData
