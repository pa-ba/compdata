{-# LANGUAGE TemplateHaskell #-}
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
     -- ** Foldable
     module Data.Comp.Derive.Foldable,
     -- ** Traversable
     module Data.Comp.Derive.Traversable,
     -- ** HaskellStrict
     module Data.Comp.Derive.HaskellStrict,
     -- ** Arbitrary
     module Data.Comp.Derive.Arbitrary,
     NFData(..),
     makeNFData,
     -- ** DeepSeq
     module Data.Comp.Derive.DeepSeq,
     -- ** Smart Constructors
     module Data.Comp.Derive.SmartConstructors,
     -- ** Smart Constructors w/ Annotations
     module Data.Comp.Derive.SmartAConstructors,
     -- ** Lifting to Sums
     liftSum
    ) where

import Control.DeepSeq (NFData (..))
import Data.Comp.Derive.Arbitrary
import Data.Comp.Derive.DeepSeq
import Data.Comp.Derive.Equality
import Data.Comp.Derive.Foldable
import Data.Comp.Derive.HaskellStrict
import Data.Comp.Derive.Ordering
import Data.Comp.Derive.Show
import Data.Comp.Derive.SmartAConstructors
import Data.Comp.Derive.SmartConstructors
import Data.Comp.Derive.Traversable
import Data.Comp.Derive.Utils (derive, liftSumGen)
import Data.Comp.Ops ((:+:), caseF)

import Language.Haskell.TH

import qualified Data.Derive.All as A
import qualified Data.DeriveTH as D

{-| Derive an instance of 'NFData' for a type constructor. -}
makeNFData :: Name -> Q [Dec]
makeNFData = D.derive A.makeNFData

{-| Given the name of a type class, where the first parameter is a functor,
  lift it to sums of functors. Example: @class ShowF f where ...@ is lifted
  as @instance (ShowF f, ShowF g) => ShowF (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseF ''(:+:)
