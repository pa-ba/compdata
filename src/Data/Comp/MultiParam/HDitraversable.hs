{-# LANGUAGE RankNTypes, FlexibleInstances, MultiParamTypeClasses,
  FlexibleContexts, OverlappingInstances, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.HDitraversable
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines traversable difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.HDitraversable
    (
     HDitraversable(..)
    ) where

import Prelude hiding (mapM, sequence, foldr)
import GHC.Prim (Any)
import Data.Maybe (fromJust)
import Data.Comp.Multi.Traversable
import Data.Comp.MultiParam.HDifunctor
import Data.Traversable
import Test.QuickCheck.Gen
import Data.Functor.Identity
import Control.Monad.Reader hiding (mapM, sequence)

{-| HDifunctors representing data structures that can be traversed from left to
  right. -}
class (HDifunctor f, Monad m) => HDitraversable f m a where
    dimapM :: NatM m b c -> NatM m (f a b) (f a c) -- (b :-> m c) -> f a b :-> m (f a c)


{-| If a difunctor is 'Traversable' for a given contravariant argument @a@, then
  it is 'HDitraversable' for all 'Monad's @m@ with the same @a@. -}
instance (HDifunctor f, Monad m, HTraversable (f a)) => HDitraversable f m a where
    dimapM = hmapM


--    dimapM f = disequence . fmap f

--    disequence :: f a (M m b) :-> M m (f a b)
--    disequence x = dimapM id (x :: f a (M m b) i)

{-
{-| If a difunctor is 'Traversable' for a given contravariant argument @a@, then
  it is 'HDitraversable' for all 'Monad's @m@ with the same @a@. -}
instance (HDifunctor f, Monad m, Traversable (f a)) => HDitraversable f m a where
    dimapM = mapM
    disequence = sequence

instance HDitraversable (->) Gen a where
    dimapM f s = MkGen run
        where run stdGen seed a = unGen (f (s a)) stdGen seed
    disequence s = MkGen run
        where run stdGen seed a = unGen (s a) stdGen seed

instance HDitraversable (->) Identity a where
    dimapM f s = Identity run
        where run a = runIdentity (f (s a))
    disequence s = Identity run
        where run a = runIdentity (s a)

instance HDitraversable (->) m a =>  HDitraversable (->) (ReaderT r m) a where
    dimapM f s = ReaderT (disequence . run)
        where run r a = runReaderT (f (s a)) r
    disequence s = ReaderT (disequence . run)
        where run r a = runReaderT (s a) r

{-| Functions of the type @Any -> Maybe a@ can be turned into functions of
 type @Maybe (Any -> a)@. The empty type @Any@ ensures that the function
 is parametric in the input, and hence the @Maybe@ monad can be pulled out. -}
instance HDitraversable (->) Maybe Any where
    disequence f = do _ <- f undefined
                      return $ \x -> fromJust $ f x-}