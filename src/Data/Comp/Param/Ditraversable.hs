{-# LANGUAGE RankNTypes, FlexibleInstances, MultiParamTypeClasses,
  FlexibleContexts, OverlappingInstances  #-}
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
import Data.Maybe (fromJust)
import Data.Comp.Param.Any
import Data.Comp.Param.Difunctor
import Data.Traversable
import Test.QuickCheck.Gen
import Data.Functor.Identity
import Control.Monad.Reader hiding (mapM, sequence)
import Control.Monad.Error hiding (mapM, sequence)
import Control.Monad.State hiding (mapM, sequence)
import Control.Monad.List hiding (mapM, sequence)
import Control.Monad.RWS hiding (Any, mapM, sequence)
import Control.Monad.Writer hiding (Any, mapM, sequence)

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
    disequence s = MkGen run
        where run stdGen seed a = unGen (s a) stdGen seed

instance Ditraversable (->) Identity a where
    dimapM f s = Identity run
        where run a = runIdentity (f (s a))
    disequence s = Identity run
        where run a = runIdentity (s a)

instance Ditraversable (->) m a =>  Ditraversable (->) (ReaderT r m) a where
    dimapM f s = ReaderT (disequence . run)
        where run r a = runReaderT (f (s a)) r
    disequence s = ReaderT (disequence . run)
        where run r a = runReaderT (s a) r


{-| Functions of the type @Any -> Maybe a@ can be turned into functions of
 type @Maybe (Any -> a)@. The empty type @Any@ ensures that the function
 is parametric in the input, and hence the @Maybe@ monad can be pulled out. -}
instance Ditraversable (->) Maybe Any where
    dimapM f g = disequence (f .g)
    disequence f = do _ <- f undefined
                      return $ \x -> fromJust $ f x


instance Ditraversable (->) (Either e) Any where
    dimapM f g = disequence (f . g)
    disequence h = case h undefined of
                   Left e -> Left e
                   Right _ -> Right $ fromRight . h
        where fromRight (Right x) = x
              fromRight (Left _) = error "fromRight: expected Right"

instance (Error e, Ditraversable (->) m Any) => Ditraversable (->) (ErrorT e m) Any where
    dimapM f g = disequence (f . g)
    disequence h = ErrorT $
                 do r <- runErrorT (h undefined) 
                    case r of
                      Left e -> return $ Left e
                      Right _ -> liftM Right $ disequence (liftM fromRight . runErrorT . h) 
        where fromRight (Right x) = x
              fromRight (Left _) = error "fromRight: expected Right"

instance (Ditraversable (->) m Any) => Ditraversable (->) (StateT s m) Any where
    dimapM f g = disequence (f . g)
    disequence h = StateT trans
        where trans s = 
                  do (_,s') <- runStateT (h undefined) s
                     fun <-  disequence (liftM fst . (`runStateT` s) . h)
                     return (fun,s')

instance (Monoid w, Ditraversable (->) m Any) => Ditraversable (->) (WriterT w m) Any where
    dimapM f g = disequence (f . g)
    disequence h = WriterT trans
        where trans = 
                  do (_,w) <- runWriterT (h undefined)
                     fun <-  disequence (liftM fst . runWriterT . h)
                     return (fun,w)

instance Ditraversable (->) [] Any where 
    dimapM f g = disequence (f . g)
    disequence h = run (h undefined) 0
        where run [] _ = []
              run (_ : xs) i = let f a = h a !! i
                               in f : run xs (i+1)

instance Ditraversable (->) m Any =>  Ditraversable (->) (ListT m) Any where 
    dimapM f g = disequence (f . g)
    disequence h = ListT $ (`run`  0) =<< runListT (h undefined)
        where run [] _ = return []
              run (_ : xs) i = do f <- disequence $ liftM (!! i) . runListT . h
                                  liftM (f :) (run xs (i+1))

instance (Monoid w, Ditraversable (->) m Any) => Ditraversable (->) (RWST r w s m) Any where
    dimapM f g = disequence (f . g)
    disequence h = RWST trans
        where trans r s = 
                  do (_,s',w) <- runRWST (h undefined) r s
                     fun <-  disequence (liftM fst' . (\ m -> runRWST m r s) . h)
                     return (fun,s',w)
              fst' (x,_,_) = x