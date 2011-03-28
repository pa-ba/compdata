{-# LANGUAGE RankNTypes, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Traversable
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines traversable difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Traversable
    (
     Ditraversable (..)
    ) where

import Prelude hiding (mapM, sequence, foldr)
import Data.Comp.Param.Functor
import Data.Comp.Param.Foldable
import Data.Traversable

class (Difunctor f, Difoldable f) => Ditraversable f where
    -- | Map each element of a structure to a monadic action, evaluate
    -- these actions from left to right, and collect the results.
    dimapM :: Monad m => (b -> m c) -> f a b -> m (f a c)

instance Ditraversable f => Traversable (f a) where
    mapM = dimapM