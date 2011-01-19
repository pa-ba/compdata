{-# LANGUAGE GADTs #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Generic
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines type generic functions and recursive schemes
-- along the lines of the Uniplate library.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Generic where

import Data.ALaCarte.Term
import Data.ALaCarte.Sum
import Data.Foldable
import Data.Traversable
import GHC.Exts
import Control.Monad hiding (mapM)
import Prelude hiding (foldl,mapM)

-- | This function returns a list of all subterms of the given
-- term. This function is similar to Uniplate's @universe@ function.
subterms :: Foldable f => Term f -> [Term f]
subterms t = build (f t)
    where f t cons nil = t `cons` foldl (\u s -> f s cons u) nil (unTerm t)
-- universe t = t : foldl (\u s -> u ++ universe s) [] (unTerm t)


-- | This function returns a list of all subterms of the given term
-- that are constructed from a particular functor.
subterms' :: (Foldable f, g :<: f) => Term f -> [g (Term f)]
subterms' (Term t) = build (f t)
    where f t cons nil = let rest = foldl (\u (Term s) -> f s cons u) nil t
                         in case proj t of
                              Just t' -> t'`cons` rest
                              Nothing -> rest

-- | This function transforms every subterm according to the given
-- function in a bottom-up manner. This function is similar to
-- Uniplate's @transform@ function.
transform :: (Functor f) => (Term f -> Term f) -> Term f -> Term f
transform f = run
    where run = f . Term . fmap run . unTerm
-- transform f  = f . Term . fmap (transform f) . unTerm


-- | Monadic version of 'transform'.
transformM :: (Traversable f, Monad m) =>
             (Term f -> m (Term f)) -> Term f -> m (Term f)
transformM  f = run 
    where run t = f =<< (liftM Term $ mapM run $ unTerm t)

-- | This function computes the generic size of the given term,
-- i.e. the its number of subterm occurrences.
size :: Foldable f => Cxt h f a -> Int
size (Hole {}) = 0
size (Term t) = foldl (\s x -> s + size x) 1 t

-- | This function computes the generic depth of the given term.
depth :: Foldable f => Cxt h f a -> Int
depth (Hole {}) = 0
depth (Term t) = 1 + foldl (\s x -> s + size x) 0 t