{-# LANGUAGE TypeOperators, FlexibleContexts #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Thunk
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines terms & contexts with thunks, with deferred
-- monadic computations.
--
--------------------------------------------------------------------------------

module Data.Comp.Thunk where

import Data.Comp.Term
import Data.Comp.Ops
import Data.Comp.Sum
import Data.Comp.Derive

import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad hiding (sequence,mapM)

import Prelude hiding (foldr, foldl,foldr1, foldl1,sequence,mapM)


data Thunk m a = Thunk (m a)

-- | This type represents terms with thunks.
type TermT m f = Term (Thunk m :+: f)

-- | This type represents contexts with thunks.
type CxtT  m h f a = Cxt h (Thunk m :+: f) a

instance Functor m => Functor (Thunk m) where
    fmap f (Thunk x) = Thunk $ fmap f x

instance Foldable m => Foldable (Thunk m) where
    fold (Thunk x) = fold x
    foldMap f (Thunk x) = foldMap f x
    foldr f e (Thunk x) = foldr f e x
    foldl f e (Thunk x) = foldl f e x
    foldr1 f (Thunk x) = foldr1 f x
    foldl1 f (Thunk x) = foldl1 f x

instance Traversable m => Traversable (Thunk m) where
    sequence (Thunk x) = liftM Thunk $ sequence x
    mapM f (Thunk x)   = liftM Thunk $ mapM f x
    sequenceA (Thunk x)    = Thunk <$> sequenceA x
    traverse f (Thunk x)    = Thunk <$> traverse f x


-- | This function turns a monadic computation into a thunk.
thunk :: (Thunk m :<: f) => m (Cxt h f a) -> Cxt h f a
thunk = inject . Thunk

-- | This function evaluates all thunks until a non-thunk node is
-- found.
dethunk :: Monad m => TermT m f -> m (f (TermT m f))
dethunk (Term (Inl (Thunk m))) = m >>= dethunk
dethunk (Term (Inr t)) = return t

-- | This function inspects the topmost non-thunk node (using
-- 'dethunk') according to the given function.
eval :: Monad m => (f (TermT m f) -> TermT m f) -> TermT m f -> TermT m f
eval cont (Term (Inl (Thunk m))) = thunk $ liftM cont $ dethunk =<< m 
eval cont (Term (Inr t)) = cont t

-- | This function inspects the topmost non-thunk nodes of two terms
-- (using 'dethunk') according to the given function.
eval2 :: Monad m => (f (TermT m f) -> f (TermT m f) -> TermT m f)
                 -> TermT m f -> TermT m f -> TermT m f
eval2 cont x y = (\ x' -> cont x' `eval` y) `eval` x 

-- | This function evaluates all thunks.
deepDethunk :: (Monad m, Traversable f) => TermT m f -> m (Term f)
deepDethunk = liftM Term . mapM deepDethunk <=< dethunk

-- | This function inspects a term (using 'deepDethunk') according to the
-- given function.
deepEval :: (Traversable f, Monad m) => 
            (Term f -> TermT m f) -> TermT m f -> TermT m f
deepEval cont v = case deepProject v of 
                    Just v' -> cont v'
                    _ -> thunk $ liftM cont $ deepDethunk v 

-- | This function inspects two terms (using 'deepDethunk') according
-- to the given function.
deepEval2 :: (Monad m, Traversable f) =>
             (Term f -> Term f -> TermT m f)
          -> TermT m f -> TermT m f -> TermT m f
deepEval2 cont x y = (\ x' -> cont x' `deepEval` y ) `deepEval` x