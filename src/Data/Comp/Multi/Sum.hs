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

module Data.Comp.Multi.Sum
    (
     (:<<:)(..),
     (:++:)(..),

     -- * Projections for Signatures and Terms
     hproj2,
     hproj3,
     hproject,
     hproject2,
     hproject3,
     deepHProject,
     deepHProject2,
     deepHProject3,
--     deepHProject',
--     deepHProject2',
--     deepHProject3',

     -- * Injections for Signatures and Terms
     hinj2,
     hinj3,
     hinject,
     hinject2,
     hinject3,
     deepHInject,
     deepHInject2,
     deepHInject3,
     deepHInjectE,
     deepHInjectE2,
     deepHInjectE3,

     -- * Injections and Projections for Constants
     hinjectHConst,
     hinjectHConst2,
     hinjectHConst3,
     hprojectHConst,
     hinjectHCxt,
     liftHCxt,
     substHHoles,
--     substHHoles'
    ) where

import Data.Comp.Multi.Functor
import Data.Comp.Multi.Traversable
import Data.Comp.Multi.ExpFunctor
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Control.Monad (liftM)

{-| A variant of 'hproj' for binary sum signatures.  -}
hproj2 :: forall f g1 g2 a i. (g1 :<<: f, g2 :<<: f) =>
          f a i -> Maybe (((g1 :++: g2) a) i)
hproj2 x = case hproj x of
             Just (y :: g1 a i) -> Just $ hinj y
             _ -> liftM hinj (hproj x :: Maybe (g2 a i))

{-| A variant of 'hproj' for ternary sum signatures.  -}
hproj3 :: forall f g1 g2 g3 a i. (g1 :<<: f, g2 :<<: f, g3 :<<: f) =>
          f a i -> Maybe (((g1 :++: g2 :++: g3) a) i)
hproj3 x = case hproj x of
             Just (y :: g1 a i) -> Just $ hinj y
             _ -> case hproj x of
                    Just (y :: g2 a i) -> Just $ hinj y
                    _ -> liftM hinj (hproj x :: Maybe (g3 a i))

-- |Project the outermost layer of a term to a sub signature.
hproject :: (g :<<: f) => NatM Maybe (HCxt h f a)  (g (HCxt h f a))
hproject (HHole _) = Nothing
hproject (HTerm t) = hproj t

-- |Project the outermost layer of a term to a binary sub signature.
hproject2 :: (g1 :<<: f, g2 :<<: f) =>
             NatM Maybe (HCxt h f a) ((g1 :++: g2) (HCxt h f a))
hproject2 (HHole _) = Nothing
hproject2 (HTerm t) = hproj2 t

-- |Project the outermost layer of a term to a ternary sub signature.
hproject3 :: (g1 :<<: f, g2 :<<: f, g3 :<<: f) =>
             NatM Maybe (HCxt h f a) ((g1 :++: g2 :++: g3) (HCxt h f a))
hproject3 (HHole _) = Nothing
hproject3 (HTerm t) = hproj3 t

-- |Project a term to a term over a sub signature.
deepHProject :: (HTraversable f, HFunctor g, g :<<: f)
             => NatM Maybe (HCxt h f a) (HCxt h g a)
deepHProject = appHSigFunM hproj

-- |Project a term to a term over a binary sub signature.
deepHProject2 :: (HTraversable f, HFunctor g1, HFunctor g2,
                  g1 :<<: f, g2 :<<: f)
              => NatM Maybe (HCxt h f a) (HCxt h (g1 :++: g2) a)
deepHProject2 = appHSigFunM hproj2

-- |Project a term to a term over a ternary sub signature.
deepHProject3 :: (HTraversable f, HFunctor g1, HFunctor g2, HFunctor g3,
                  g1 :<<: f, g2 :<<: f, g3 :<<: f)
              => NatM Maybe (HCxt h f a) (HCxt h (g1 :++: g2 :++: g3) a)
deepHProject3 = appHSigFunM hproj3

{-| A variant of 'hinj' for binary sum signatures.  -}
hinj2 :: (f1 :<<: g, f2 :<<: g) => (f1 :++: f2) a :-> g a
hinj2 (HInl x) = hinj x
hinj2 (HInr y) = hinj y

{-| A variant of 'hinj' for ternary sum signatures.  -}
hinj3 :: (f1 :<<: g, f2 :<<: g, f3 :<<: g) => (f1 :++: f2 :++: f3) a :-> g a
hinj3 (HInl x) = hinj x
hinj3 (HInr y) = hinj2 y

-- |Inject a term where the outermost layer is a sub signature.
hinject :: (g :<<: f) => g (HCxt h f a) :-> HCxt h f a
hinject = HTerm . hinj

-- |Inject a term where the outermost layer is a binary sub signature.
hinject2 :: (f1 :<<: g, f2 :<<: g) => (f1 :++: f2) (HCxt h g a) :-> HCxt h g a
hinject2 = HTerm . hinj2

-- |Inject a term where the outermost layer is a ternary sub signature.
hinject3 :: (f1 :<<: g, f2 :<<: g, f3 :<<: g)
         => (f1 :++: f2 :++: f3) (HCxt h g a) :-> HCxt h g a
hinject3 = HTerm . hinj3

-- |Inject a term over a sub signature to a term over larger signature.
deepHInject :: (HFunctor g, HFunctor f, g :<<: f) => HCxt h g a :-> HCxt h f a
deepHInject = appHSigFun hinj

-- |Inject a term over a binary sub signature to a term over larger signature.
deepHInject2 :: (HFunctor f1, HFunctor f2, HFunctor g, f1 :<<: g, f2 :<<: g)
             => HCxt h (f1 :++: f2) a :-> HCxt h g a
deepHInject2 = appHSigFun hinj2

-- |Inject a term over a ternary sub signature to a term over larger signature.
deepHInject3 :: (HFunctor f1, HFunctor f2, HFunctor f3, HFunctor g,
                 f1 :<<: g, f2 :<<: g, f3 :<<: g)
             => HCxt h (f1 :++: f2 :++: f3) a :-> HCxt h g a
deepHInject3 = appHSigFun hinj3

{-| A variant of 'deepHInject' for exponential signatures. -}
deepHInjectE :: (HExpFunctor g, g :<<: f) => HTerm g :-> HTerm f
deepHInjectE = hcataE hinject

{-| A variant of 'deepHInject2' for exponential signatures. -}
deepHInjectE2 :: (HExpFunctor g1, HExpFunctor g2, g1 :<<: f, g2 :<<: f) =>
                 HTerm (g1 :++: g2) :-> HTerm f
deepHInjectE2 = hcataE hinject2

{-| A variant of 'deepHInject3' for exponential signatures. -}
deepHInjectE3 :: (HExpFunctor g1, HExpFunctor g2, HExpFunctor g3,
                  g1 :<<: f, g2 :<<: f, g3 :<<: f) =>
                 HTerm (g1 :++: g2 :++: g3) :-> HTerm f
deepHInjectE3 = hcataE hinject3

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

hinjectHConst2 :: (HFunctor f1, HFunctor f2, HFunctor g, f1 :<<: g, f2 :<<: g)
               => HConst (f1 :++: f2) :-> HCxt h g a
hinjectHConst2 = hinject2 . hfmap (const undefined)

hinjectHConst3 :: (HFunctor f1, HFunctor f2, HFunctor f3, HFunctor g,
                   f1 :<<: g, f2 :<<: g, f3 :<<: g)
               => HConst (f1 :++: f2 :++: f3) :-> HCxt h g a
hinjectHConst3 = hinject3 . hfmap (const undefined)

hprojectHConst :: (HFunctor g, g :<<: f) => NatM Maybe (HCxt h f a) (HConst g)
hprojectHConst = fmap (hfmap (const (K ()))) . hproject