{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Difunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines difunctors (Meijer, Hutton, FPCA '95), i.e. binary type
-- constructors that are contravariant in the first argument and covariant in
-- the second argument.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Difunctor
    (
     Difunctor (..)
    ) where

-- | This class represents difunctors, i.e. binary type constructors that are
-- contravariant in the first argument and covariant in the second argument.
class Difunctor f where
    dimap :: (a -> b) -> (c -> d) -> f b c -> f a d

instance Difunctor (->) where
    dimap f g h = g . h . f

instance Difunctor f => Functor (f a) where
    fmap = dimap id