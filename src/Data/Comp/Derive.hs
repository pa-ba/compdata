--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.Derive (
  module Data.Comp.Derive.Show,
  module Data.Comp.Derive.Ordering,
  module Data.Comp.Derive.Equality,
  module Data.Comp.Derive.Arbitrary,
  module Data.Comp.Derive.SmartConstructors,
  module Data.Comp.Derive.SmartMConstructors,
  module Data.Comp.Derive.DeepSeq,
  module Data.Comp.Derive.Foldable,
  module Data.Comp.Derive.Traversable,
  module Data.Comp.Derive.HFunctor,
  module Data.Comp.Derive.HFoldable,
  module Data.Comp.Derive.HTraversable,
  module Data.Comp.Derive.HShow,
  module Data.Comp.Derive.HEquality,
  module Data.Comp.Derive.ExpFunctor,
  module Control.DeepSeq,
  instanceFunctor,
  instanceNFData,
  derive ) where


import Control.DeepSeq
import Data.Comp.Derive.HEquality
import Data.Comp.Derive.HShow
import Data.Comp.Derive.HFunctor
import Data.Comp.Derive.HFoldable
import Data.Comp.Derive.HTraversable
import Data.Comp.Derive.Foldable
import Data.Comp.Derive.Traversable
import Data.Comp.Derive.DeepSeq
import Data.Comp.Derive.Show
import Data.Comp.Derive.Ordering
import Data.Comp.Derive.Equality
import Data.Comp.Derive.Arbitrary
import Data.Comp.Derive.SmartConstructors
import Data.Comp.Derive.SmartMConstructors
import Data.Comp.Derive.ExpFunctor

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
