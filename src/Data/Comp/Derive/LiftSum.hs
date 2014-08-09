{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
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
     liftSum,
     caseF
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Ops ((:+:) (..))
import Data.Comp.Sum
import Language.Haskell.TH hiding (Cxt)


{-| Given the name of a type class, where the first parameter is a functor,
  lift it to sums of functors. Example: @class ShowF f where ...@ is lifted
  as @instance (ShowF f, ShowF g) => ShowF (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseF ''(:+:)



{-| Utility function to case on a functor sum, without exposing the internal
  representation of sums. -}
caseF :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
{-# INLINE caseF #-}
caseF f g x = case x of
                Inl x -> f x
                Inr x -> g x
