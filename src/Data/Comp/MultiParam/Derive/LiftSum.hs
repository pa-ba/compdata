{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for higher-order difunctors to sums of higher-order
-- difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Derive.LiftSum
    (
     liftSum
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.MultiParam.Sum
import Data.Comp.MultiParam.Ops ((:+:), caseHD)

{-| Given the name of a type class, where the first parameter is a higher-order
  difunctor, lift it to sums of higher-order difunctors. Example:
  @class ShowHD f where ...@ is lifted as
  @instance (ShowHD f, ShowHD g) => ShowHD (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseHD ''(:+:)