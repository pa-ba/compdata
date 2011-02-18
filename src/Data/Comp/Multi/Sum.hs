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
  hproject,
  deepHProject,
  hprojectHConst,
  hinject,
  hinjectHCxt,
  hinjectHConst,
  liftHCxt,
  deepHInject,
  substHHoles,
   ) where

import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra

-- |Project a sub term from a compound term.
hproject :: (g :<<: f) => NatM Maybe (HCxt h f a)  (g (HCxt h f a))
hproject (HHole _) = Nothing
hproject (HTerm t) = hproj t

-- |Project a sub term recursively from a term.
deepHProject :: (HTraversable f, HFunctor g, g :<<: f)
            => NatM Maybe (HCxt h f a) (HCxt h g a)
deepHProject = appHSigFunM hproj


-- |Inject a term into a compound term.
hinject :: (g :<<: f) => g (HCxt h f a) :-> HCxt h f a
hinject = HTerm . hinj

-- | Deep injection function.

deepHInject  :: (HFunctor g, HFunctor f, g :<<: f)
            => HCxt h g a :-> HCxt h f a
deepHInject = appHSigFun hinj

-- | This function injects a whole context into another context.
hinjectHCxt :: (HFunctor g, g :<<: f) => HCxt h' g (HCxt h f a) :-> HCxt h f a
hinjectHCxt = hcata' hinject

-- | This function lifts the given functor to a context.
liftHCxt :: (HFunctor f, g :<<: f) => g a :-> HContext f a
liftHCxt g = simpHCxt $ hinj g

-- | This function applies the given context with hole type @a@ to a
-- family @f@ of contexts (possibly terms) indexed by @a@. That is,
-- each hole @h@ is replaced by the context @f h@.

substHHoles :: (HFunctor f, HFunctor g, f :<<: g)
           => (v :-> HCxt h g a) -> HCxt h' f v :-> HCxt h g a
substHHoles f c = hinjectHCxt $ hfmap f c

hinjectHConst :: (HFunctor g, g :<<: f) => HConst g :-> HCxt h f a
hinjectHConst = hinject . hfmap (const undefined)

hprojectHConst :: (HFunctor g, g :<<: f) => NatM Maybe (HCxt h f a) (HConst g)
hprojectHConst = fmap (hfmap (const (K ()))) . hproject