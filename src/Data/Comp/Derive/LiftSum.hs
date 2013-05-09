{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for difunctors to sums of functors.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.LiftSum
    (
     liftSum
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Sum
import Data.Comp.Ops ((:+:), caseF)


{-| Given the name of a type class, where the first parameter is a functor,
  lift it to sums of functors. Example: @class ShowF f where ...@ is lifted
  as @instance (ShowF f, ShowF g) => ShowF (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseF ''(:+:)
