{-# LANGUAGE TypeOperators, GADTs, ScopedTypeVariables, IncoherentInstances,
  RankNTypes #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Sum
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines sums on signatures. All definitions are
-- generalised versions of those in "Data.Comp.Sum".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Sum (
  (:<<:)(..),
  (:++:)(..),
  project,
  deepProject,
  projectHConst,
  inject,
  injectHCxt,
  injectHConst,
  liftHCxt,
  deepInject,
  substHHoles,
   ) where

import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra

-- |Project a sub term from a compound term.
project :: (g :<<: f) => NatM Maybe (HCxt h f a)  (g (HCxt h f a))
project (HHole _) = Nothing
project (HTerm t) = hproj t

-- |Project a sub term recursively from a term.
deepProject :: (HTraversable f, HFunctor g, g :<<: f)
            => NatM Maybe (HCxt h f a) (HCxt h g a)
deepProject = appHSigFunM hproj


-- |Inject a term into a compound term.
inject :: (g :<<: f) => g (HCxt h f a) :-> HCxt h f a
inject = HTerm . hinj

-- | Deep injection function.

deepInject  :: (HFunctor g, HFunctor f, g :<<: f)
            => HCxt h g a :-> HCxt h f a
deepInject = appHSigFun hinj

-- | This function injects a whole context into another context.

injectHCxt :: (HFunctor g, g :<<: f) => HCxt h' g (HCxt h f a) :-> HCxt h f a
injectHCxt = hcata' inject

-- | This function lifts the given functor to a context.
liftHCxt :: (HFunctor f, g :<<: f) => g a :-> HContext f a
liftHCxt g = simpHCxt $ hinj g

-- | This function applies the given context with hole type @a@ to a
-- family @f@ of contexts (possibly terms) indexed by @a@. That is,
-- each hole @h@ is replaced by the context @f h@.

substHHoles :: (HFunctor f, HFunctor g, f :<<: g)
           => (v :-> HCxt h g a) -> HCxt h' f v :-> HCxt h g a
substHHoles f c = injectHCxt $ hfmap f c

injectHConst :: (HFunctor g, g :<<: f) => HConst g :-> HCxt h f a
injectHConst = inject . hfmap (const undefined)

projectHConst :: (HFunctor g, g :<<: f) => NatM Maybe (HCxt h f a) (HConst g)
projectHConst = fmap (hfmap (const (K ()))) . project