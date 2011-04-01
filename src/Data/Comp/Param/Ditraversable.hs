{-# LANGUAGE RankNTypes, FlexibleInstances, MultiParamTypeClasses,
  FlexibleContexts, IncoherentInstances, EmptyDataDecls #-}
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
     Ditraversable(..),
     Nothing
    ) where

import Prelude hiding (mapM, sequence, foldr)
import Data.Comp.Param.Difunctor
import Data.Traversable
import Data.Maybe (fromJust)

{-| An empty type. @Nothing@ is used to emulate parametricity, e.g. a function
  @Nothing -> a[Nothing]@ is equivalent with @forall b. b -> a@, but the former
  avoids the impredicative typing extension. -}
data Nothing

instance Eq Nothing where
instance Ord Nothing where
instance Show Nothing where

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

instance Ditraversable (->) Maybe Nothing where
    disequence f = do _ <- f undefined
                      return $ \x -> fromJust $ f x