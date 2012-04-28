{-# LANGUAGE TypeOperators #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Number
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

module Data.Comp.Multi.Number 
    ( Numbered (..)
    , unNumbered
    , number
    , HTraversable ()) where

import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Ordering
import Data.Comp.Multi.Equality


import Control.Monad.State


-- | This type is used for numbering components of a functorial value.
newtype Numbered a i = Numbered (Int, a i)

unNumbered :: Numbered a :-> a
unNumbered (Numbered (_, x)) = x

instance KEq (Numbered a) where
  keq (Numbered (i,_))  (Numbered (j,_)) = i == j

instance KOrd (Numbered a) where
    kcompare (Numbered (i,_))  (Numbered (j,_)) = i `compare` j

-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
number :: HTraversable f => f a :-> f (Numbered a)
number x = fst $ runState (hmapM run x) 0 where
  run b = do n <- get
             put (n+1)
             return $ Numbered (n,b)
