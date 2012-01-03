--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Number
-- Copyright   :  (c) 2012 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
-- 
-- This module provides functionality to number the components of a
-- functorial value with consecutive integers.
--
--------------------------------------------------------------------------------

module Data.Comp.Number 
    ( Numbered (..)
    , unNumbered
    , number
    , Traversable ()) where

import Data.Traversable

import Control.Monad.State hiding (mapM)
import Prelude hiding (mapM)


-- | This type is used for numbering components of a functorial value.
newtype Numbered a = Numbered (Int, a)

unNumbered :: Numbered a -> a
unNumbered (Numbered (_, x)) = x

instance Eq (Numbered a) where
    Numbered (i,_) == Numbered (j,_) = i == j

instance Ord (Numbered a) where
    compare (Numbered (i,_))  (Numbered (j,_)) = i `compare` j

-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
number :: Traversable f => f a -> f (Numbered a)
number x = fst $ runState (mapM run x) 0 where
  run b = do n <- get
             put (n+1)
             return $ Numbered (n,b)