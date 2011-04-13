{-# LANGUAGE RankNTypes, FlexibleInstances, MultiParamTypeClasses,
  FlexibleContexts, OverlappingInstances #-}
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

import Prelude hiding (mapM, sequence, foldr)
import Data.Comp.Param.Difunctor
import Data.Traversable
import Test.QuickCheck.Gen
import Data.Functor.Identity
import Control.Monad.Reader hiding (mapM, sequence)

{-| Difunctors representing data structures that can be traversed from left to
  right. -}
class (Difunctor f, Monad m) => Ditraversable f m a where
    dimapM :: (b -> m c) -> f a b -> m (f a c)
    dimapM f = disequence . fmap f

    disequence :: f a (m b) -> m (f a b)
    disequence = dimapM id

{-| If a difunctor is 'Traversable' for a given contravariant argument @a@, then
  it is 'Ditraversable' for all 'Monad's @m@ with the same @a@. -}
instance (Difunctor f, Monad m, Traversable (f a)) => Ditraversable f m a where
    dimapM = mapM
    disequence = sequence

instance Ditraversable (->) Gen a where
    dimapM f s = MkGen run
        where run stdGen seed a = unGen (f (s a)) stdGen seed

instance Ditraversable (->) Identity a where
    dimapM f s = Identity run
        where run a = runIdentity (f (s a))

instance Ditraversable (->) (ReaderT r Identity) a where
    dimapM f s = ReaderT (Identity . run)
        where run r a = runIdentity $ runReaderT (f (s a)) r

instance Ditraversable (->) m a =>  Ditraversable (->) (ReaderT r m) a where
    dimapM f s = ReaderT (disequence . run)
        where run r a = runReaderT (f (s a)) r