{-# LANGUAGE Rank2Types #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.MonadTrm
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the type class @MonadTrm@.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.MonadTrm
    (
     MonadTrm(..)
    ) where

import Data.Maybe (fromJust)
import Data.Comp.Param.Term

{-| Monads for which embedded @Trm@ values, which are parametric at top level,
  can be made into monadic @Term@ values, i.e. \"pushing the parametricity
  inwards\". -}
class Monad m => MonadTrm m where
    trmM :: (forall a. m (Trm f a)) -> m (Term f)

instance MonadTrm Maybe where
    trmM Nothing = Nothing
    trmM x       = Just (Term $ fromJust x)

instance MonadTrm (Either a) where
    trmM (Left x) = Left x
    trmM x        = Right (Term $ fromRight x)
                             where fromRight :: Either a b -> b
                                   fromRight (Right x) = x
                                   fromRight _ = error "fromRight: Left"

instance MonadTrm [] where
    trmM [] = []
    trmM l  = Term (head l) : trmM (tail l)