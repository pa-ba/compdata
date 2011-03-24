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
import Data.Comp.Param.Term

class Difunctor f => Ditraversable f where
    -- | Map each element of a structure to a monadic action, evaluate
    -- these actions from left to right, and collect the results.
    dimapM :: (Functor g, Monad m) => (b -> m (g c)) -> f a b -> m (f a (g c))
--    dimapM :: (Difunctor g, Monad m, a :< b) => (Cxt f a b -> m (Cxt g a b)) -> f a (Cxt f a b) -> m (Cxt g a b) --f a (g a))
--    dimapM f x = disequence $ fmap f x

-- a :< b
-- f a (Cxt f a b)
-- forall a b. (a :< b) => Cxt f a b -> m (Cxt g a b)

    -- | Evaluate each monadic action in the structure from left to right,
    -- and collect the results.
    disequence :: (Functor g, Monad m, a :< b) => f a (m (g b)) -> m (f a (g b))
    disequence = dimapM id