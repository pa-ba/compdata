{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, ScopedTypeVariables, RankNTypes #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Generic
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines type generic functions and recursive schemes
-- along the lines of the Uniplate library.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Generic where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.HFunctor
import GHC.Exts
import Control.Monad
import Prelude

import Data.Maybe

-- | This function returns a list of all subterms of the given
-- term. This function is similar to Uniplate's @universe@ function.
subterms :: forall f  . HFoldable f => Term f  :=> [A (Term f)]
subterms t = build (f t)
    where f :: Term f :=> (A (Term f) -> b -> b) -> b -> b
          f t cons nil = A t `cons` hfoldl (\u s -> f s cons u) nil (unTerm t)

-- | This function returns a list of all subterms of the given term
-- that are constructed from a particular functor.
subterms' :: forall f g . (HFoldable f, g :<<: f) => Term f :=> [A (g (Term f))]
subterms' (Term t) = build (f t)
    where f :: f (Term f) :=> (A (g (Term f)) -> b -> b) -> b -> b
          f t cons nil = let rest = hfoldl (\u (Term s) -> f s cons u) nil t
                         in case hproj t of
                              Just t' -> A t' `cons` rest
                              Nothing -> rest

-- | This function transforms every subterm according to the given
-- function in a bottom-up manner. This function is similar to
-- Uniplate's @transform@ function.
transform :: forall f . (HFunctor f) => (Term f :-> Term f) -> Term f :-> Term f
transform f = run
    where run :: Term f :-> Term f
          run = f . Term . hfmap run . unTerm


-- | Monadic version of 'transform'.
transformM :: forall f m . (HTraversable f, Monad m) =>
             (NatM m (Term f) (Term f)) -> NatM m (Term f) (Term f)
transformM  f = run 
    where run :: NatM m (Term f) (Term f)
          run t = f =<< (liftM Term $ hmapM run $ unTerm t)

query :: HFoldable f => (Term f :=>  r) -> (r -> r -> r) -> Term f :=> r
-- query q c = run 
--     where run i@(Term t) = foldl (\s x -> s `c` run x) (q i) t
query q c i@(Term t) = hfoldl (\s x -> s `c` query q c x) (q i) t

subs :: HFoldable f => Term f  :=> [A (Term f)]
subs = query (\x-> [A x]) (++)

subs' :: (HFoldable f, g :<<: f) => Term f :=> [A (g (Term f))]
subs' = catMaybes . map pr . subs
        where pr (A v) = fmap A (project v)

-- | This function computes the generic size of the given term,
-- i.e. the its number of subterm occurrences.
size :: HFoldable f => Cxt h f a :=> Int
size (Hole {}) = 0
size (Term t) = hfoldl (\s x -> s + size x) 1 t

-- | This function computes the generic depth of the given term.
depth :: HFoldable f => Cxt h f a :=> Int
depth (Hole {}) = 0
depth (Term t) = 1 + hfoldl (\s x -> s + size x) 0 t