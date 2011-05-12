{-# LANGUAGE TypeOperators, GADTs, ScopedTypeVariables, IncoherentInstances,
  RankNTypes, FlexibleContexts #-}
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
     (:<:)(..),
     (:+:),

     -- * Projections for Signatures and Terms
     proj2,
     proj3,
     project,
     project2,
     project3,
     deepProject,
     deepProject2,
     deepProject3,
     deepProject',
     deepProject2',
     deepProject3',

     -- * Injections for Signatures and Terms
     inj2,
     inj3,
     inject,
     inject2,
     inject3,
     deepInject,
     deepInject2,
     deepInject3,

     -- * Injections and Projections for Constants
     injectConst,
     injectConst2,
     injectConst3,
     projectConst,
     injectCxt,
     liftCxt,
     substHoles,
--     substHoles'
    ) where

import Data.Comp.Multi.Functor
import Data.Comp.Multi.Traversable
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Control.Monad (liftM)

{-| A variant of 'proj' for binary sum signatures.  -}
proj2 :: forall f g1 g2 a i. (g1 :<: f, g2 :<: f) =>
          f a i -> Maybe (((g1 :+: g2) a) i)
proj2 x = case proj x of
             Just (y :: g1 a i) -> Just $ inj y
             _ -> liftM inj (proj x :: Maybe (g2 a i))

{-| A variant of 'proj' for ternary sum signatures.  -}
proj3 :: forall f g1 g2 g3 a i. (g1 :<: f, g2 :<: f, g3 :<: f) =>
          f a i -> Maybe (((g1 :+: g2 :+: g3) a) i)
proj3 x = case proj x of
             Just (y :: g1 a i) -> Just $ inj y
             _ -> case proj x of
                    Just (y :: g2 a i) -> Just $ inj y
                    _ -> liftM inj (proj x :: Maybe (g3 a i))

-- |Project the outermost layer of a term to a sub signature.
project :: (g :<: f) => NatM Maybe (Cxt h f a)  (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = proj t

-- |Project the outermost layer of a term to a binary sub signature.
project2 :: (g1 :<: f, g2 :<: f) =>
             NatM Maybe (Cxt h f a) ((g1 :+: g2) (Cxt h f a))
project2 (Hole _) = Nothing
project2 (Term t) = proj2 t

-- |Project the outermost layer of a term to a ternary sub signature.
project3 :: (g1 :<: f, g2 :<: f, g3 :<: f) =>
             NatM Maybe (Cxt h f a) ((g1 :+: g2 :+: g3) (Cxt h f a))
project3 (Hole _) = Nothing
project3 (Term t) = proj3 t

-- |Project a term to a term over a sub signature.
deepProject :: (HTraversable f, g :<: f)  => CxtFunM Maybe f g
deepProject = appSigFunM proj

-- |Project a term to a term over a binary sub signature.
deepProject2 :: (HTraversable f, g1 :<: f, g2 :<: f)
             => CxtFunM Maybe f (g1 :+: g2)
deepProject2 = appSigFunM proj2

-- |Project a term to a term over a ternary sub signature.
deepProject3 :: (HTraversable f, g1 :<: f, g2 :<: f, g3 :<: f)
              => CxtFunM Maybe f (g1 :+: g2 :+: g3)
deepProject3 = appSigFunM proj3

-- |Project a term to a term over a sub signature.
deepProject' :: (HTraversable g, g :<: f)  => CxtFunM Maybe f g
deepProject' = appSigFunM' proj

-- |Project a term to a term over a binary sub signature.
deepProject2' :: (HTraversable (g1 :+: g2), g1 :<: f, g2 :<: f)
             => CxtFunM Maybe f (g1 :+: g2)
deepProject2' = appSigFunM' proj2

-- |Project a term to a term over a ternary sub signature.
deepProject3' :: (HTraversable (g1 :+: g2 :+: g3), g1 :<: f, g2 :<: f, g3 :<: f)
              => CxtFunM Maybe f (g1 :+: g2 :+: g3)
deepProject3' = appSigFunM' proj3

{-| A variant of 'inj' for binary sum signatures.  -}
inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a :-> g a
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

{-| A variant of 'inj' for ternary sum signatures.  -}
inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a :-> g a
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |Inject a term where the outermost layer is a sub signature.
inject :: (g :<: f) => g (Cxt h f a) :-> Cxt h f a
inject = Term . inj

-- |Inject a term where the outermost layer is a binary sub signature.
inject2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) (Cxt h g a) :-> Cxt h g a
inject2 = Term . inj2

-- |Inject a term where the outermost layer is a ternary sub signature.
inject3 :: (f1 :<: g, f2 :<: g, f3 :<: g)
         => (f1 :+: f2 :+: f3) (Cxt h g a) :-> Cxt h g a
inject3 = Term . inj3

-- |Inject a term over a sub signature to a term over larger signature.
deepInject :: (HFunctor g, HFunctor f, g :<: f) => Cxt h g a :-> Cxt h f a
deepInject = appSigFun inj

-- |Inject a term over a binary sub signature to a term over larger signature.
deepInject2 :: (HFunctor f1, HFunctor f2, HFunctor g, f1 :<: g, f2 :<: g)
             => Cxt h (f1 :+: f2) a :-> Cxt h g a
deepInject2 = appSigFun inj2

-- |Inject a term over a ternary sub signature to a term over larger signature.
deepInject3 :: (HFunctor f1, HFunctor f2, HFunctor f3, HFunctor g,
                 f1 :<: g, f2 :<: g, f3 :<: g)
             => Cxt h (f1 :+: f2 :+: f3) a :-> Cxt h g a
deepInject3 = appSigFun inj3

-- | This function injects a whole context into another context.
injectCxt :: (HFunctor g, g :<: f) => Cxt h' g (Cxt h f a) :-> Cxt h f a
injectCxt = cata' inject

-- | This function lifts the given functor to a context.
liftCxt :: (HFunctor f, g :<: f) => g a :-> Context f a
liftCxt g = simpCxt $ inj g

-- | This function applies the given context with hole type @a@ to a
-- family @f@ of contexts (possibly terms) indexed by @a@. That is,
-- each hole @h@ is replaced by the context @f h@.

substHoles :: (HFunctor f, HFunctor g, f :<: g)
           => (v :-> Cxt h g a) -> Cxt h' f v :-> Cxt h g a
substHoles f c = injectCxt $ hfmap f c

injectConst :: (HFunctor g, g :<: f) => Const g :-> Cxt h f a
injectConst = inject . hfmap (const undefined)

injectConst2 :: (HFunctor f1, HFunctor f2, HFunctor g, f1 :<: g, f2 :<: g)
               => Const (f1 :+: f2) :-> Cxt h g a
injectConst2 = inject2 . hfmap (const undefined)

injectConst3 :: (HFunctor f1, HFunctor f2, HFunctor f3, HFunctor g,
                   f1 :<: g, f2 :<: g, f3 :<: g)
               => Const (f1 :+: f2 :+: f3) :-> Cxt h g a
injectConst3 = inject3 . hfmap (const undefined)

projectConst :: (HFunctor g, g :<: f) => NatM Maybe (Cxt h f a) (Const g)
projectConst = fmap (hfmap (const (K ()))) . project