{-# LANGUAGE GADTs, ExistentialQuantification, TypeOperators, ScopedTypeVariables, RankNTypes #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Generic
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines type generic functions and recursive schemes
-- along the lines of the Uniplate library. All definitions are
-- generalised versions of those in "Data.Comp.Generic".
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
subterms :: forall f  . HFoldable f => HTerm f  :=> [A (HTerm f)]
subterms t = build (f t)
    where f :: HTerm f :=> (A (HTerm f) -> b -> b) -> b -> b
          f t cons nil = A t `cons` hfoldl (\u s -> f s cons u) nil (unHTerm t)

-- | This function returns a list of all subterms of the given term
-- that are constructed from a particular functor.
subterms' :: forall f g . (HFoldable f, g :<: f) => HTerm f :=> [A (g (HTerm f))]
subterms' (HTerm t) = build (f t)
    where f :: f (HTerm f) :=> (A (g (HTerm f)) -> b -> b) -> b -> b
          f t cons nil = let rest = hfoldl (\u (HTerm s) -> f s cons u) nil t
                         in case hproj t of
                              Just t' -> A t' `cons` rest
                              Nothing -> rest

-- | This function transforms every subterm according to the given
-- function in a bottom-up manner. This function is similar to
-- Uniplate's @transform@ function.
transform :: forall f . (HFunctor f) => (HTerm f :-> HTerm f) -> HTerm f :-> HTerm f
transform f = run
    where run :: HTerm f :-> HTerm f
          run = f . HTerm . hfmap run . unHTerm


-- | Monadic version of 'transform'.
transformM :: forall f m . (HTraversable f, Monad m) =>
             NatM m (HTerm f) (HTerm f) -> NatM m (HTerm f) (HTerm f)
transformM  f = run 
    where run :: NatM m (HTerm f) (HTerm f)
          run t = f =<< liftM HTerm $ hmapM run $ unHTerm t

query :: HFoldable f => (HTerm f :=>  r) -> (r -> r -> r) -> HTerm f :=> r
-- query q c = run 
--     where run i@(HTerm t) = foldl (\s x -> s `c` run x) (q i) t
query q c i@(HTerm t) = hfoldl (\s x -> s `c` query q c x) (q i) t

subs :: HFoldable f => HTerm f  :=> [A (HTerm f)]
subs = query (\x-> [A x]) (++)

subs' :: (HFoldable f, g :<: f) => HTerm f :=> [A (g (HTerm f))]
subs' = mapMaybe . subs
        where pr (A v) = fmap A (project v)

-- | This function computes the generic size of the given term,
-- i.e. the its number of subterm occurrences.
size :: HFoldable f => HCxt h f a :=> Int
size (HHole {}) = 0
size (HTerm t) = hfoldl (\s x -> s + size x) 1 t

-- | This function computes the generic depth of the given term.
depth :: HFoldable f => HCxt h f a :=> Int
depth (HHole {}) = 0
depth (HTerm t) = 1 + hfoldl (\s x -> s + size x) 0 t