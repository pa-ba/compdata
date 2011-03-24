{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, ScopedTypeVariables, GADTs, MultiParamTypeClasses, UndecidableInstances, IncoherentInstances, EmptyDataDecls #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Traversable
-- Copyright   :  (c) 2011 Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines difunctors, i.e. binary type constructors that are
-- contravariant in the first argument and covariant in the second argument.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Traversable
    (
     Ditraversable (..)
    ) where

import Prelude hiding (mapM, sequence, foldr)
import Data.Comp.Param.Functor

class Difunctor t => Ditraversable t where
    -- | Map each element of a structure to a monadic action, evaluate
    -- these actions from left to right, and collect the results.
    dimapM :: (Functor f, Monad m) => (a -> m (f b)) -> t b a -> m (t b (f b))
    dimapM f x = disequence $ fmap f x

    -- | Evaluate each monadic action in the structure from left to right,
    -- and collect the results.
    disequence :: (Functor f, Monad m) => t a (m (f a)) -> m (t a (f a))
    disequence = dimapM id