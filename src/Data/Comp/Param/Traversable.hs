{-# LANGUAGE RankNTypes, FlexibleInstances, MultiParamTypeClasses,
  FlexibleContexts, IncoherentInstances #-}
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
import Data.Traversable

class (Difunctor f, Monad m) => Ditraversable f m a where
    dimapM :: (b -> m c) -> f a b -> m (f a c)
    dimapM f = disequence . fmap f

    disequence :: f a (m b) -> m (f a b)
    disequence = dimapM id

instance (Difunctor f, Monad m, Traversable (f a)) => Ditraversable f m a where
    dimapM = mapM
    disequence = sequence