{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ditraversable
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines traversable difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Ditraversable
    (
     Ditraversable(..)
    ) where

import Data.Comp.Param.Difunctor
import Data.Functor.Identity
import Control.Monad.Reader hiding (mapM, sequence)

{-| Difunctors representing data structures that can be traversed from left to
  right. -}
class (Difunctor f, Monad m) => Ditraversable f m where
    dimapM :: (b -> m c) -> f a b -> m (f a c)
    dimapM f = disequence . fmap f
    disequence :: f a (m b) -> m (f a b)
    disequence = dimapM id

instance Ditraversable (->) Identity where
    dimapM f s = Identity run
        where run a = runIdentity (f (s a))
    disequence s = Identity run
        where run a = runIdentity (s a)

instance Ditraversable (->) m => Ditraversable (->) (ReaderT r m) where
    dimapM f s = ReaderT (disequence . run)
        where run r a = runReaderT (f (s a)) r
    disequence s = ReaderT (disequence . run)
        where run r a = runReaderT (s a) r