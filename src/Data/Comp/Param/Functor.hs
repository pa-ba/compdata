{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, ScopedTypeVariables, GADTs, MultiParamTypeClasses, UndecidableInstances, IncoherentInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Functor
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

module Data.Comp.Param.Functor
    (
     Difunctor (..)
    ) where

-- | This class represents difunctors, i.e. binary type constructors that are
-- contravariant in the first argument and covariant in the second argument.
class Difunctor f where
    dimap :: (a -> b) -> (c -> d) -> (f b c -> f a d)

instance Difunctor f => Functor (f a) where
    fmap = dimap id