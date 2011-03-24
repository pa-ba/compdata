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
import Data.Comp.Param.Sub ((:<))

class Difunctor f => Ditraversable f where
    -- | Map each element of a structure to a monadic action, evaluate
    -- these actions from left to right, and collect the results.
    dimapM :: (Functor g, Monad m, a :< c) => (b -> m (g c))
           -> f a b -> m (f a (g c))
    dimapM f = disequence . fmap f

    -- | Evaluate each monadic action in the structure from left to right,
    -- and collect the results.
    disequence :: (Functor g, Monad m, a :< b) => f a (m (g b)) -> m (f a (g b))
    disequence = dimapM id