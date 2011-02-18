--------------------------------------------------------------------------------
-- |
-- Module	: Data.Comp.ExpFunctor
-- Copyright 	: 2008 Edward Kmett
-- License	: BSD
--
-- Maintainer	: Tom Hvitved <hvitved@diku.dk>
-- Stability	: unknown
-- Portability	: unknown
--
-- Exponential functors, see <http://comonad.com/reader/2008/rotten-bananas/>.
--------------------------------------------------------------------------------

module Data.Comp.ExpFunctor
    ( ExpFunctor(..)
    ) where

{-| Exponential functors are functors that may be both covariant (as ordinary
 functors) and contravariant. -}
class ExpFunctor f where
    xmap :: (a -> b) -> (b -> a) -> f a -> f b
