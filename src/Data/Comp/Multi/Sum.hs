{-# LANGUAGE TypeOperators, GADTs, ScopedTypeVariables, IncoherentInstances,
  Rank2Types, FlexibleContexts, TemplateHaskell #-}
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
     (:<:),
     (:+:),
     caseH,

     -- * Projections for Signatures and Terms
     proj,
     proj2,
     proj3,
     proj4,
     proj5,
     proj6,
     proj7,
     proj8,
     proj9,
     proj10,
     project,
     project2,
     project3,
     project4,
     project5,
     project6,
     project7,
     project8,
     project9,
     project10,
     deepProject,
     deepProject2,
     deepProject3,
     deepProject4,
     deepProject5,
     deepProject6,
     deepProject7,
     deepProject8,
     deepProject9,
     deepProject10,

     -- * Injections for Signatures and Terms
     inj,
     inj2,
     inj3,
     inj4,
     inj5,
     inj6,
     inj7,
     inj8,
     inj9,
     inj10,
     inject,
     inject2,
     inject3,
     inject4,
     inject5,
     inject6,
     inject7,
     inject8,
     inject9,
     inject10,
     deepInject,
     deepInject2,
     deepInject3,
     deepInject4,
     deepInject5,
     deepInject6,
     deepInject7,
     deepInject8,
     deepInject9,
     deepInject10,

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

import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Derive.Projections
import Data.Comp.Multi.Derive.Injections
import Control.Monad (liftM)

$(liftM concat $ mapM projn [2..10])

-- |Project the outermost layer of a term to a sub signature. If the signature
-- @g@ is compound of /n/ atomic signatures, use @project@/n/ instead.
project :: (g :<: f) => NatM Maybe (Cxt h f a) (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = proj t

$(liftM concat $ mapM projectn [2..10])

-- | Tries to coerce a term/context to a term/context over a sub-signature. If
-- the signature @g@ is compound of /n/ atomic signatures, use
-- @deepProject@/n/ instead.
deepProject :: (HTraversable g, g :<: f)  => CxtFunM Maybe f g
{-# INLINE deepProject #-}
deepProject = appSigFunM' proj

$(liftM concat $ mapM deepProjectn [2..10])
{-# INLINE deepProject2 #-}
{-# INLINE deepProject3 #-}
{-# INLINE deepProject4 #-}
{-# INLINE deepProject5 #-}
{-# INLINE deepProject6 #-}
{-# INLINE deepProject7 #-}
{-# INLINE deepProject8 #-}
{-# INLINE deepProject9 #-}
{-# INLINE deepProject10 #-}

$(liftM concat $ mapM injn [2..10])

-- |Inject a term where the outermost layer is a sub signature. If the signature
-- @g@ is compound of /n/ atomic signatures, use @inject@/n/ instead.
inject :: (g :<: f) => g (Cxt h f a) :-> Cxt h f a
inject = Term . inj

$(liftM concat $ mapM injectn [2..10])

-- |Inject a term over a sub signature to a term over larger signature. If the
-- signature @g@ is compound of /n/ atomic signatures, use @deepInject@/n/
-- instead.
deepInject :: (HFunctor g, g :<: f) => CxtFun g f
{-# INLINE deepInject #-}
deepInject = appSigFun inj

$(liftM concat $ mapM deepInjectn [2..10])
{-# INLINE deepInject2 #-}
{-# INLINE deepInject3 #-}
{-# INLINE deepInject4 #-}
{-# INLINE deepInject5 #-}
{-# INLINE deepInject6 #-}
{-# INLINE deepInject7 #-}
{-# INLINE deepInject8 #-}
{-# INLINE deepInject9 #-}
{-# INLINE deepInject10 #-}

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