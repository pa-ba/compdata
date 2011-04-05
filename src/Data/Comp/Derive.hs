--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module contains functionality for automatically deriving boilerplate
-- code using Template Haskell. Examples include instances of 'Functor',
-- 'Foldable', and 'Traversable'.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive
    (
     derive,
     -- |Derive boilerplate instances for compositional data type signatures.

     -- ** ShowF
     module Data.Comp.Derive.Show,
     -- ** EqF
     module Data.Comp.Derive.Equality,
     -- ** OrdF
     module Data.Comp.Derive.Ordering,
     -- ** Functor
     Functor,
     instanceFunctor,
     -- ** Foldable
     module Data.Comp.Derive.Foldable,
     -- ** Traversable
     module Data.Comp.Derive.Traversable,
     -- ** Arbitrary
     module Data.Comp.Derive.Arbitrary,
     NFData(..),
     instanceNFData,
     -- ** DeepSeq
     module Data.Comp.Derive.DeepSeq,
     -- ** Smart Constructors
     module Data.Comp.Derive.SmartConstructors,
     -- ** Smart Constructors w/ Annotations
     module Data.Comp.Derive.SmartAConstructors,
     -- ** Lifting to Sums
     module Data.Comp.Derive.LiftSum
    ) where

import Control.DeepSeq (NFData(..))
import Data.Comp.Derive.Utils (derive)
import Data.Comp.Derive.Foldable
import Data.Comp.Derive.Traversable
import Data.Comp.Derive.DeepSeq
import Data.Comp.Derive.Show
import Data.Comp.Derive.Ordering
import Data.Comp.Derive.Equality
import Data.Comp.Derive.Arbitrary
import Data.Comp.Derive.SmartConstructors
import Data.Comp.Derive.SmartAConstructors
import Data.Comp.Derive.LiftSum

import Language.Haskell.TH

import qualified Data.DeriveTH as D
import Data.Derive.All

{-| Derive an instance of 'Functor' for a type constructor of any first-order
  kind taking at least one argument. -}
instanceFunctor :: Name -> Q [Dec]
instanceFunctor = D.derive makeFunctor

{-| Derive an instance of 'NFData' for a type constructor. -}
instanceNFData :: Name -> Q [Dec]
instanceNFData = D.derive makeNFData
