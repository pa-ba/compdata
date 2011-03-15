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
     -- * First-order Signatures
     -- |Derive boilerplate instances for first-order signatures, i.e.
     -- signatures for ordinary compositional data types.

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

     -- * Higher-order Signatures
     -- |Derive boilerplate instances for higher-order signatures, i.e.
     -- signatures for generalised compositional data types.

     -- ** HShowF
     module Data.Comp.Derive.Multi.Show,
     -- ** HEqF
     module Data.Comp.Derive.Multi.Equality,
     -- ** HFunctor
     module Data.Comp.Derive.Multi.Functor,
     -- ** HFoldable
     module Data.Comp.Derive.Multi.Foldable,
     -- ** HTraversable
     module Data.Comp.Derive.Multi.Traversable,
     -- ** Smart Constructors
     module Data.Comp.Derive.Multi.SmartConstructors
    ) where

import Control.DeepSeq (NFData(..))
import Data.Comp.Derive.Foldable
import Data.Comp.Derive.Traversable
import Data.Comp.Derive.DeepSeq
import Data.Comp.Derive.Show
import Data.Comp.Derive.Ordering
import Data.Comp.Derive.Equality
import Data.Comp.Derive.Arbitrary
import Data.Comp.Derive.SmartConstructors
import Data.Comp.Derive.Multi.Equality
import Data.Comp.Derive.Multi.Show
import Data.Comp.Derive.Multi.Functor
import Data.Comp.Derive.Multi.Foldable
import Data.Comp.Derive.Multi.Traversable
import Data.Comp.Derive.Multi.SmartConstructors

import Language.Haskell.TH
import Control.Monad

import qualified Data.DeriveTH as D
import Data.Derive.All

{-| Helper function for generating a list of instances for a list of named
 signatures. For example, in order to derive instances 'Functor' and
 'ShowF' for a signature @Exp@, use derive as follows (requires Template
 Haskell):

 > $(derive [instanceFunctor, instanceShowF] [''Exp])
 -}
derive :: [Name -> Q [Dec]] -> [Name] -> Q [Dec]
derive ders names = liftM concat $ sequence [der name | der <- ders, name <- names]

{-| Derive an instance of 'Functor' for a type constructor of any first-order
  kind taking at least one argument. -}
instanceFunctor :: Name -> Q [Dec]
instanceFunctor = D.derive makeFunctor

{-| Derive an instance of 'NFData' for a type constructor. -}
instanceNFData :: Name -> Q [Dec]
instanceNFData = D.derive makeNFData
