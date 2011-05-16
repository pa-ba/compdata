{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
  FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Sum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides the infrastructure to extend signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Sum
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
     liftCxt
    ) where

import Prelude hiding (sequence)
import Control.Monad hiding (sequence)
import Data.Comp.Param.Term
import Data.Comp.Param.Algebra
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable

{-| A variant of 'proj' for binary sum signatures.  -}
proj2 :: forall f g1 g2 a b. (g1 :<: f, g2 :<: f) => f a b
      -> Maybe ((g1 :+: g2) a b)
proj2 x = case proj x of
            Just (y :: g1 a b) -> Just $ inj y
            _ -> liftM inj (proj x :: Maybe (g2 a b))

{-| A variant of 'proj' for ternary sum signatures.  -}
proj3 :: forall f g1 g2 g3 a b. (g1 :<: f, g2 :<: f, g3 :<: f) => f a b
      -> Maybe ((g1 :+: g2 :+: g3) a b)
proj3 x = case proj x of
            Just (y :: g1 a b) -> Just $ inj y
            _ -> case proj x of
                   Just (y :: g2 a b) -> Just $ inj y
                   _ -> liftM inj (proj x :: Maybe (g3 a b))

-- |Project the outermost layer of a term to a sub signature.
project :: (g :<: f) => Cxt h f a b -> Maybe (g a (Cxt h f a b))
project (Term t) = proj t
project (Hole _) = Nothing
project (Place _) = Nothing

-- |Project the outermost layer of a term to a binary sub signature.
project2 :: (g1 :<: f, g2 :<: f) => Cxt h f a b
         -> Maybe ((g1 :+: g2) a (Cxt h f a b))
project2 (Term t) = proj2 t
project2 (Hole _) = Nothing
project2 (Place _) = Nothing

-- |Project the outermost layer of a term to a ternary sub signature.
project3 :: (g1 :<: f, g2 :<: f, g3 :<: f) => Cxt h f a b
         -> Maybe ((g1 :+: g2 :+: g3) a (Cxt h f a b))
project3 (Term t) = proj3 t
project3 (Hole _) = Nothing
project3 (Place _) = Nothing


-- | Tries to coerce a term/context to a term/context over a
-- sub-signature.
deepProject :: (Ditraversable g Maybe Any, g :<: f)
             => CxtFunM Maybe f g
{-# INLINE deepProject #-}
deepProject = appSigFunM' proj


-- | This is a variant of 'deepProject' that can be used if the target
-- signature cannot be derived as being a sub-signature of the source
-- signature directly but its decomposition into two summands can.
deepProject2 :: (Ditraversable (g1 :+: g2) Maybe Any,
                  g1 :<: f, g2 :<: f)
              => CxtFunM Maybe f (g1 :+: g2)
{-# INLINE deepProject2 #-}
deepProject2 = appSigFunM' proj2

-- | This is a variant of 'deepProject' that can be used if the target
-- signature cannot be derived as being a sub-signature of the source
-- signature directly but its decomposition into three summands can.
deepProject3 :: (Ditraversable (g1 :+: g2 :+: g3) Maybe Any,
                  g1 :<: f, g2 :<: f, g3 :<: f)
              => CxtFunM Maybe f (g1 :+: g2 :+: g3)
{-# INLINE deepProject3 #-}
deepProject3 = appSigFunM' proj3

{-| A variant of 'inj' for binary sum signatures.  -}
inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a b -> g a b
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

{-| A variant of 'inj' for ternary sum signatures.  -}
inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a b -> g a b
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |Inject a term where the outermost layer is a sub signature.
inject :: (g :<: f) => g a (Cxt h f a b) -> Cxt h f a b
inject = Term . inj

-- |Inject a term where the outermost layer is a binary sub signature.
inject2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a (Cxt h g a b) -> Cxt h g a b
inject2 = Term . inj2

-- |Inject a term where the outermost layer is a ternary sub signature.
inject3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a (Cxt h g a b)
        -> Cxt h g a b
inject3 = Term . inj3

-- |Inject a term over a sub signature to a term over larger signature.
deepInject :: (Difunctor g, g :<: f) => CxtFun g f
{-# INLINE deepInject #-}
deepInject = appSigFun inj

-- |Inject a term over a binary sub signature to a term over larger signature.
deepInject2 :: (Difunctor (f1 :+: f2), f1 :<: g, f2 :<: g)
            => CxtFun (f1 :+: f2) g
{-# INLINE deepInject2 #-}
deepInject2 = appSigFun inj2

-- |Inject a term over a ternary signature to a term over larger signature.
deepInject3 :: (Difunctor (f1 :+: f2 :+: f3), f1 :<: g, f2 :<: g, f3 :<: g)
            => CxtFun (f1 :+: f2 :+: f3) g
{-# INLINE deepInject3 #-}
deepInject3 =  appSigFun inj3

injectConst :: (Difunctor g, g :<: f) => Const g -> Cxt h f Any a
injectConst = inject . fmap (const undefined)

injectConst2 :: (Difunctor f1, Difunctor f2, Difunctor g, f1 :<: g, f2 :<: g)
             => Const (f1 :+: f2) -> Cxt h g Any a
injectConst2 = inject2 . fmap (const undefined)

injectConst3 :: (Difunctor f1, Difunctor f2, Difunctor f3, Difunctor g,
                 f1 :<: g, f2 :<: g, f3 :<: g)
             => Const (f1 :+: f2 :+: f3) -> Cxt h g Any a
injectConst3 = inject3 . fmap (const undefined)

projectConst :: (Difunctor g, g :<: f) => Cxt h f Any a -> Maybe (Const g)
projectConst = fmap (fmap (const ())) . project

{-| This function injects a whole context into another context. -}
injectCxt :: (Difunctor g, g :<: f) => Cxt h g a (Cxt h f a b) -> Cxt h f a b
injectCxt (Term t) = inject $ fmap injectCxt t
injectCxt (Hole x) = x
injectCxt (Place p) = Place p

{-| This function lifts the given functor to a context. -}
liftCxt :: (Difunctor f, g :<: f) => g a b -> Cxt Hole f a b
liftCxt g = simpCxt $ inj g

instance (Show (f a b), Show (g a b)) => Show ((f :+: g) a b) where
    show (Inl v) = show v
    show (Inr v) = show v

instance (Ord (f a b), Ord (g a b)) => Ord ((f :+: g) a b) where
    compare (Inl _) (Inr _) = LT
    compare (Inr _) (Inl _) = GT
    compare (Inl x) (Inl y) = compare x y
    compare (Inr x) (Inr y) = compare x y

instance (Eq (f a b), Eq (g a b)) => Eq ((f :+: g) a b) where
    (Inl x) == (Inl y) = x == y
    (Inr x) == (Inr y) = x == y                   
    _ == _ = False