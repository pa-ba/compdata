{-# LANGUAGE TypeOperators, KindSignatures, GADTs,
ScopedTypeVariables, IncoherentInstances, RankNTypes #-}

module Data.ALaCarte.Multi.Sum (
  (:<<:)(..),
  (:++:)(..),
  project,
  deepProject,
  projectConst,
  inject,
  injectCxt,
  injectConst,
  liftCxt,
  deepInject,
  substHoles,
   ) where

import Data.ALaCarte.Multi.HFunctor
import Data.ALaCarte.Multi.Ops
import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.Algebra

-- |Project a sub term from a compound term.
project :: (g :<<: f) => NatM Maybe (Cxt h f a)  (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = hproj t

-- |Project a sub term recursively from a term.
deepProject :: (HTraversable f, HFunctor g, g :<<: f)
            => NatM Maybe (Cxt h f a) (Cxt h g a)
deepProject = applySigFunM hproj


-- |Inject a term into a compound term.
inject :: (g :<<: f) => g (Cxt h f a) :-> Cxt h f a
inject = Term . hinj

-- | Deep injection function.

deepInject  :: (HFunctor g, HFunctor f, g :<<: f)
            => Cxt h g a :-> Cxt h f a
deepInject = applySigFun hinj

-- | This function injects a whole context into another context.

injectCxt :: (HFunctor g, g :<<: f) => Cxt h' g (Cxt h f a) :-> Cxt h f a
injectCxt = cata' inject

-- | This function lifts the given functor to a context.
liftCxt :: (HFunctor f, g :<<: f) => g a :-> Context f a
liftCxt g = simpCxt $ hinj g

-- | This function applies the given context with hole type @a@ to a
-- family @f@ of contexts (possibly terms) indexed by @a@. That is,
-- each hole @h@ is replaced by the context @f h@.

substHoles :: (HFunctor f, HFunctor g, f :<<: g)
           => (v :-> Cxt h g a) -> Cxt h' f v :-> Cxt h g a
substHoles f c = injectCxt $ hfmap f c

injectConst :: (HFunctor g, g :<<: f) => Const g :-> Cxt h f a
injectConst = inject . hfmap (const undefined)

projectConst :: (HFunctor g, g :<<: f) => NatM Maybe (Cxt h f a) (Const g)
projectConst = fmap (hfmap (const (K ()))) . project