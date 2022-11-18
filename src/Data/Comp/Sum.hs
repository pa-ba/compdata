{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Sum
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides the infrastructure to extend signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Sum
    (
     (:<:),
     (:=:),
     (:+:),
     caseF,

     -- * Projections for Signatures and Terms
     proj,
     project,
     deepProject,
     project_,
     deepProject_,

     -- * Injections for Signatures and Terms
     inj,
     inject,
     deepInject,
     inject_,
     deepInject_,

     split,

     -- * Injections and Projections for Constants
     injectConst,
     projectConst,
     injectCxt,
     liftCxt,
     substHoles,
     substHoles'
    ) where

import Data.Comp.Algebra
import Data.Comp.Ops
import Data.Comp.Term

import Control.Monad hiding (mapM, sequence)
import Prelude hiding (mapM, sequence)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe


-- |Project the outermost layer of a term to a sub signature.
project :: (g :<: f) => Cxt h f a -> Maybe (g (Cxt h f a))
project = project_ proj

-- |Project the outermost layer of a term to a sub signature.
project_ :: SigFunM Maybe f g -> Cxt h f a -> Maybe (g (Cxt h f a))
project_ _ (Hole _) = Nothing
project_ f (Term t) = f t


-- | Tries to coerce a term\/context to a ter\/context over a sub-signature.
deepProject :: (Traversable g, g :<: f) => CxtFunM Maybe f g
{-# INLINE deepProject #-}
deepProject = appSigFunM' proj

-- | Tries to coerce a term\/context to a term\/context over a sub-signature.
deepProject_ :: (Traversable g) => (SigFunM Maybe f g) -> CxtFunM Maybe f g
{-# INLINE deepProject_ #-}
deepProject_ = appSigFunM'


-- |Inject a term where the outermost layer is a sub signature.
inject :: (g :<: f) => g (Cxt h f a) -> Cxt h f a
inject = inject_ inj

-- |Inject a term where the outermost layer is a sub signature.
inject_ :: SigFun g f -> g (Cxt h f a) -> Cxt h f a
inject_ f = Term . f


-- |Inject a term over a sub signature to a term over larger signature.
deepInject :: (Functor g, g :<: f) => CxtFun g f
{-# INLINE deepInject #-}
deepInject = deepInject_ inj

-- |Inject a term over a sub signature to a term over larger signature.
deepInject_ :: (Functor g) => SigFun g f -> CxtFun g f
{-# INLINE deepInject_ #-}
deepInject_ = appSigFun


split :: (f :=: f1 :+: f2) => (f1 (Term f) -> a) -> (f2 (Term f) -> a) -> Term f -> a
split f1 f2 (Term t) = spl f1 f2 t

injectConst :: (Functor g, g :<: f) => Const g -> Cxt h f a
injectConst = inject . fmap (const undefined)


projectConst :: (Functor g, g :<: f) => Cxt h f a -> Maybe (Const g)
projectConst = fmap (fmap (const ())) . project

{-| This function injects a whole context into another context. -}
injectCxt :: (Functor g, g :<: f) => Cxt h' g (Cxt h f a) -> Cxt h f a
injectCxt = cata' inject

{-| This function lifts the given functor to a context. -}
liftCxt :: (Functor f, g :<: f) => g a -> Context f a
liftCxt g = simpCxt $ inj g

{-| This function applies the given context with hole type @a@ to a
family @f@ of contexts (possibly terms) indexed by @a@. That is, each
hole @h@ is replaced by the context @f h@. -}

substHoles :: (Functor f, Functor g, f :<: g) => Cxt h' f v -> (v -> Cxt h g a) -> Cxt h g a
substHoles c f = injectCxt $ fmap f c

substHoles' :: (Functor f, Functor g, f :<: g, Ord v) => Cxt h' f v -> Map v (Cxt h g a) -> Cxt h g a
substHoles' c m = substHoles c (fromJust . (`Map.lookup`  m))


instance (Show (f a), Show (g a)) => Show ((f :+: g) a) where
    show (Inl v) = show v
    show (Inr v) = show v


instance (Ord (f a), Ord (g a)) => Ord ((f :+: g) a) where
    compare (Inl _) (Inr _) = LT
    compare (Inr _) (Inl _) = GT
    compare (Inl x) (Inl y) = compare x y
    compare (Inr x) (Inr y) = compare x y


instance (Eq (f a), Eq (g a)) => Eq ((f :+: g) a) where
    (Inl x) == (Inl y) = x == y
    (Inr x) == (Inr y) = x == y
    _ == _ = False
