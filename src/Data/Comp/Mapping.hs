{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Mapping
-- Copyright   :  (c) 2014 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides functionality to construct mappings from
-- positions in a functorial value.
--
--------------------------------------------------------------------------------

module Data.Comp.Mapping
    ( Numbered (..)
    , unNumbered
    , number
    , Traversable ()
    , Mapping (..)
    , prodMap
    , lookupNumMap) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Traversable

import Control.Monad.State hiding (mapM)
import Prelude hiding (mapM)


-- | This type is used for numbering components of a functorial value.
data Numbered a = Numbered Int a

unNumbered :: Numbered a -> a
unNumbered (Numbered _ x) = x


-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
number :: Traversable f => f a -> f (Numbered a)
number x = evalState (mapM run x) 0 where
  run b = do n <- get
             put (n+1)
             return $ Numbered n b


infix 1 |->
infixr 0 &


class Functor m => Mapping m k | m -> k where
    -- | left-biased union of two mappings.
    (&) :: m v -> m v -> m v

    -- | This operator constructs a singleton mapping.
    (|->) :: k -> v -> m v

    -- | This is the empty mapping.
    empty :: m v

    -- | This function constructs the pointwise product of two maps each
    -- with a default value.
    prodMapWith :: (v1 -> v2 -> v) -> v1 -> v2 -> m v1 -> m v2 -> m v

    -- | Returns the value at the given key or returns the given
    -- default when the key is not an element of the map.
    findWithDefault :: a -> k -> m a -> a

-- | This function constructs the pointwise product of two maps each
-- with a default value.
prodMap :: Mapping m k => v1 -> v2 -> m v1 -> m v2 -> m (v1, v2)
prodMap = prodMapWith (,)

newtype NumMap k v = NumMap (IntMap v) deriving Functor

lookupNumMap :: a -> Int -> NumMap t a -> a
lookupNumMap d k (NumMap m) = IntMap.findWithDefault d k m

instance Mapping (NumMap k) (Numbered k) where
    NumMap m1 & NumMap m2 = NumMap (IntMap.union m1 m2)
    Numbered k _ |-> v = NumMap $ IntMap.singleton k v
    empty = NumMap IntMap.empty

    findWithDefault d (Numbered i _) m = lookupNumMap d i m

    prodMapWith f p q (NumMap mp) (NumMap mq) = NumMap $ IntMap.mergeWithKey merge 
                                          (IntMap.map (`f` q)) (IntMap.map (p `f`)) mp mq
      where merge _ p q = Just (p `f` q)
