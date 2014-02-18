{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
  FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
  ScopedTypeVariables, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Sum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides the infrastructure to extend signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Sum
    (
     (:<:),
     (:+:),
     caseHD,

     -- * Projections for Signatures and Terms
     proj,
     project,
     deepProject,

     -- * Injections for Signatures and Terms
     inj,
     inject,
     deepInject,

     injectCxt,
     liftCxt
    ) where

import Prelude hiding (sequence)
import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.Algebra
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.HDitraversable



-- |Project the outermost layer of a term to a sub signature. If the signature
-- @g@ is compound of /n/ atomic signatures, use @project@/n/ instead.
project :: (g :<: f) => NatM Maybe (Cxt h f a b) (g a (Cxt h f a b))
project (In t)   = proj t
project (Hole _) = Nothing
project (Var _)  = Nothing


-- | Tries to coerce a term/context to a term/context over a sub-signature. If
-- the signature @g@ is compound of /n/ atomic signatures, use
-- @deepProject@/n/ instead.
deepProject :: (HDitraversable g, g :<: f) => Term f i -> Maybe (Term g i)
{-# INLINE deepProject #-}
deepProject = appTSigFunM' proj


-- |Inject a term where the outermost layer is a sub signature. If the signature
-- @g@ is compound of /n/ atomic signatures, use @inject@/n/ instead.
inject :: (g :<: f) => g a (Cxt h f a b) :-> Cxt h f a b
inject = In . inj


-- |Inject a term over a sub signature to a term over larger signature. If the
-- signature @g@ is compound of /n/ atomic signatures, use @deepInject@/n/
-- instead.
deepInject :: (HDifunctor g, g :<: f) => CxtFun g f
{-# INLINE deepInject #-}
deepInject = appSigFun inj


{-| This function injects a whole context into another context. -}
injectCxt :: (HDifunctor g, g :<: f) => Cxt h g a (Cxt h f a b) :-> Cxt h f a b
injectCxt (In t) = inject $ hfmap injectCxt t
injectCxt (Hole x) = x
injectCxt (Var p) = Var p

{-| This function lifts the given functor to a context. -}
liftCxt :: (HDifunctor f, g :<: f) => g a b :-> Cxt Hole f a b
liftCxt g = simpCxt $ inj g

instance (Show (f a b i), Show (g a b i)) => Show ((f :+: g) a b i) where
    show (Inl v) = show v
    show (Inr v) = show v

instance (Ord (f a b i), Ord (g a b i)) => Ord ((f :+: g) a b i) where
    compare (Inl _) (Inr _) = LT
    compare (Inr _) (Inl _) = GT
    compare (Inl x) (Inl y) = compare x y
    compare (Inr x) (Inr y) = compare x y

instance (Eq (f a b i), Eq (g a b i)) => Eq ((f :+: g) a b i) where
    (Inl x) == (Inl y) = x == y
    (Inr x) == (Inr y) = x == y                   
    _ == _ = False
