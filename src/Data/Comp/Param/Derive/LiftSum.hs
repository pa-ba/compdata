{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for difunctors to sums of difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive.LiftSum
    (
     liftSum
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops ((:+:), caseD)

{-| Given the name of a type class, where the first parameter is a difunctor,
  lift it to sums of difunctors. Example: @class ShowD f where ...@ is lifted
  as @instance (ShowD f, ShowD g) => ShowD (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseD ''(:+:)