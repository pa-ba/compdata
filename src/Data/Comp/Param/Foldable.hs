{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, ScopedTypeVariables,
  GADTs, MultiParamTypeClasses, UndecidableInstances, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Foldable
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines foldable difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Foldable
    (
     Difoldable (..)
    ) where

import Data.Foldable
import Data.Comp.Param.Functor

class Difunctor f => Difoldable f where
    -- | Left-associative fold of a structure.
    difoldl :: (a -> b -> a) -> a -> f c b -> a

instance Difoldable f => Foldable (f a) where
    foldl = difoldl