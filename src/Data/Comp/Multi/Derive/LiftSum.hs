{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for higher-order functors to sums of higher-order
-- functors.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Derive.LiftSum
    (
     liftSum
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Ops ((:+:), caseH)

{-| Given the name of a type class, where the first parameter is a higher-order
  functor, lift it to sums of higher-order. Example: @class HShowF f where ...@
  is lifted as @instance (HShowF f, HShowF g) => HShowF (f :+: g) where ... @.
 -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseH ''(:+:)