{-# LANGUAGE RankNTypes, FlexibleInstances, MultiParamTypeClasses,
  FlexibleContexts, OverlappingInstances, TypeOperators, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.HDitraversable
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines traversable higher-order difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.HDitraversable
    (
     HDitraversable (..),
     HTraversable (..)
    ) where

import Prelude hiding (mapM, sequence, foldr)
import Data.Comp.Multi.HTraversable
import Data.Comp.MultiParam.HDifunctor

{-| HDifunctors representing data structures that can be traversed from left to
  right. -}
class (HDifunctor f, Monad m) => HDitraversable f m where
    hdimapM :: NatM m b c -> NatM m (f a b) (f a c)