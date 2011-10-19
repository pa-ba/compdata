{-# LANGUAGE TypeOperators, FlexibleContexts, RankNTypes #-}

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

module Data.Comp.Thunk
    (TermT
    ,CxtT
    ,thunk
    ,whnf
    ,whnf'
    ,whnfPr
    ,nf
    ,eval
    ,eval2
    ,deepEval
    ,deepEval2
    ,(#>)
    ,(#>>)
    ,AlgT
    ,strict
    ,strictAt) where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Ops
import Data.Comp.Sum
import Data.Comp.Derive
import Data.Comp.Zippable

import qualified Data.Set as Set

import Data.Traversable
import Control.Monad hiding (sequence,mapM)

import Prelude hiding (foldr, foldl,foldr1, foldl1,sequence,mapM)


-- | This type represents terms with thunks.
type TermT m f = Term (m :+: f)

-- | This type represents contexts with thunks.
type CxtT  m h f a = Cxt h  (m :+: f) a


-- | This function turns a monadic computation into a thunk.
thunk :: (m :<: f) => m (Cxt h f a) -> Cxt h f a
thunk = inject

-- | This function evaluates all thunks until a non-thunk node is
-- found.
whnf :: Monad m => TermT m f -> m (f (TermT m f))
whnf (Term (Inl m)) = m >>= whnf
whnf (Term (Inr t)) = return t

whnf' :: Monad m => TermT m f -> m (TermT m f)
whnf' = liftM inject . whnf

-- | This function first evaluates the argument term into whnf via
-- 'whnf' and then projects the top-level signature to the desired
-- subsignature. Failure to do the projection is signalled as a
-- failure in the monad.
whnfPr :: (Monad m, g :<: f) => TermT m f -> m (g (TermT m f))
whnfPr t = do res <- whnf t
              case proj res of
                Just res' -> return res'
                Nothing -> fail "projection failed"

-- | This function inspects the topmost non-thunk node (using
-- 'whnf') according to the given function.
eval :: Monad m => (f (TermT m f) -> TermT m f) -> TermT m f -> TermT m f
eval cont (Term (Inl m)) = thunk $ cont' =<< whnf =<< m 
    where cont' = return . cont
    -- alt: where cont' x = liftM inject $ whnf $ cont x
eval cont (Term (Inr t)) = cont t

infixl 1 #>

-- | Variant of 'eval' with flipped argument positions
(#>) :: Monad m => TermT m f -> (f (TermT m f) -> TermT m f) -> TermT m f
(#>) = flip eval

-- | This function inspects the topmost non-thunk nodes of two terms
-- (using 'whnf') according to the given function.
eval2 :: Monad m => (f (TermT m f) -> f (TermT m f) -> TermT m f)
                 -> TermT m f -> TermT m f -> TermT m f
eval2 cont x y = (\ x' -> cont x' `eval` y) `eval` x 

-- | This function evaluates all thunks.
nf :: (Monad m, Traversable f) => TermT m f -> m (Term f)
nf = liftM Term . mapM nf <=< whnf

-- | This function inspects a term (using 'nf') according to the
-- given function.
deepEval :: (Traversable f, Monad m) => 
            (Term f -> TermT m f) -> TermT m f -> TermT m f
deepEval cont v = case deepProject v of 
                    Just v' -> cont v'
                    _ -> thunk $ liftM cont $ nf v 

infixl 1 #>>

-- | Variant of 'deepEval' with flipped argument positions
(#>>) :: (Monad m, Traversable f) => TermT m f -> (Term f -> TermT m f) -> TermT m f
(#>>) = flip deepEval

-- | This function inspects two terms (using 'nf') according
-- to the given function.
deepEval2 :: (Monad m, Traversable f) =>
             (Term f -> Term f -> TermT m f)
          -> TermT m f -> TermT m f -> TermT m f
deepEval2 cont x y = (\ x' -> cont x' `deepEval` y ) `deepEval` x

-- | This type represents algebras which have terms with thunks as
-- carrier.
type AlgT m f g = Alg f (TermT m g)

-- | This combinator makes the evaluation of the given functor
-- application strict by evaluating all thunks of immediate subterms.
strict :: (f :<: g, Traversable f, Monad m) => f (TermT m g) -> TermT m g
strict x = thunk $ liftM inject $ mapM whnf' x

-- | This type represents position representations for a functor
-- @f@. It is a function that extracts a number of components (of
-- polymorphic type @a@) from a functorial value and puts it into a
-- list.
type Pos f = forall a . Ord a => f a -> [a]

-- | This combinator is a variant of 'strict' that only makes a subset
-- of the arguments of a functor application strict. The first
-- argument of this combinator specifies which positions are supposed
-- to be strict.
strictAt :: (f :<: g, Traversable f, Zippable f, Monad m) => Pos f ->  f (TermT m g) -> TermT m g
strictAt p s = thunk $ liftM inject $ mapM run s'
    where s'  = number s
          isStrict e = Set.member e $ Set.fromList $ p s'
          run e | isStrict e = whnf' $ unNumbered e
                | otherwise  = return $ unNumbered e
