{-# LANGUAGE TypeOperators, RankNTypes #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.ExpFunctor
-- Copyright   :  (c) 2011 Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines higher-order exponential functors.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.ExpFunctor
    (
      HExpFunctor(..)
    ) where

import Data.Comp.Multi.Functor

{-| Higher-order exponential functors are higher-order functors that may be both covariant (as ordinary higher-order functors) and contravariant. -}
class HExpFunctor f where
    hxmap :: (a :-> b) -> (b :-> a) -> f a :-> f b