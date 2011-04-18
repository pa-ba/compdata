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
import Data.Comp.Multi.Traversable
import Data.Comp.MultiParam.HDifunctor
{-import Data.Traversable
import Test.QuickCheck.Gen
import Data.Functor.Identity
import Control.Monad.Reader hiding (mapM, sequence)-}

{-| HDifunctors representing data structures that can be traversed from left to
  right. -}
class (HDifunctor f, Monad m) => HDitraversable f m a where
    hdimapM :: NatM m b c -> NatM m (f a b) (f a c)

{-| If a higher-order difunctor is 'HTraversable' for a given contravariant
  argument @a@, then it is 'HDitraversable' for all 'Monad's @m@ with the same
  @a@. -}
instance (HDifunctor f, Monad m, HTraversable (f a)) => HDitraversable f m a where
    hdimapM = hmapM

{-instance HDitraversable (:~>) Gen a where
    hdimapM f ((:~>) s) = MkGen run
        where run stdGen seed a = unGen (f (s a)) stdGen seed

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