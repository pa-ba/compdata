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
     (:+:)(..),

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
     liftCxt
    ) where

import Prelude hiding (sequence)
import Control.Monad hiding (sequence)
import Data.Comp.Param.Term
import Data.Comp.Param.Algebra
import Data.Comp.Param.Ops
import Data.Comp.Param.Functor
import Data.Comp.Param.Traversable

{-| A variant of 'proj' for binary sum signatures.  -}
proj2 :: forall f g1 g2 a e. (g1 :<: f, g2 :<: f) => f a e
      -> Maybe ((g1 :+: g2) a e)
proj2 x = case proj x of
            Just (y :: g1 a e) -> Just $ inj y
            _ -> liftM inj (proj x :: Maybe (g2 a e))

{-| A variant of 'proj' for ternary sum signatures.  -}
proj3 :: forall f g1 g2 g3 a e. (g1 :<: f, g2 :<: f, g3 :<: f) => f a e
      -> Maybe ((g1 :+: g2 :+: g3) a e)
proj3 x = case proj x of
            Just (y :: g1 a e) -> Just $ inj y
            _ -> case proj x of
                   Just (y :: g2 a e) -> Just $ inj y
                   _ -> liftM inj (proj x :: Maybe (g3 a e))

-- |Project the outermost layer of a term to a sub signature.
project :: (g :<: f) => Cxt f a b -> Maybe (g a (Cxt f a b))
project (Hole _) = Nothing
project (Term t) = proj t

-- |Project the outermost layer of a term to a binary sub signature.
project2 :: (g1 :<: f, g2 :<: f) => Cxt f a b
         -> Maybe ((g1 :+: g2) a (Cxt f a b))
project2 (Hole _) = Nothing
project2 (Term t) = proj2 t

-- |Project the outermost layer of a term to a ternary sub signature.
project3 :: (g1 :<: f, g2 :<: f, g3 :<: f) => Cxt f a b
         -> Maybe ((g1 :+: g2 :+: g3) a (Cxt f a b))
project3 (Hole _) = Nothing
project3 (Term t) = proj3 t

-- |Project a term to a term over a sub signature.
deepProject :: (Ditraversable f Maybe a, Difunctor g, g :<: f, a :< b)
            => Cxt f a b -> Maybe (Cxt g a b)
deepProject = appSigFunM proj

-- |Project a term to a term over a binary sub signature.
deepProject2 :: (Ditraversable f Maybe a, Difunctor g1, Difunctor g2,
                 g1 :<: f, g2 :<: f, a :< b)
             => Cxt f a b -> Maybe (Cxt (g1 :+: g2) a b)
deepProject2 = appSigFunM proj2

-- |Project a term to a term over a ternary sub signature.
deepProject3 :: (Ditraversable f Maybe a, Difunctor g1, Difunctor g2,
                 Difunctor g3, g1 :<: f, g2 :<: f, g3 :<: f, a :< b)
             => Cxt f a b -> Maybe (Cxt (g1 :+: g2 :+: g3) a b)
deepProject3 = appSigFunM proj3

-- |A variant of 'deepProject' where the sub signature is required to be
-- 'Traversable rather than the whole signature.
deepProject' :: forall g f a b. (Ditraversable g Maybe a, g :<: f, a :< b)
             => Cxt f a b -> Maybe (Cxt g a b)
deepProject' (Hole x) = return $ Hole x
deepProject' (Term t) = do
  v <- proj t
  v' <- dimapM deepProject' v
  return $ Term v'

-- |A variant of 'deepProject2' where the sub signatures are required to be
-- 'Traversable rather than the whole signature.
deepProject2' :: forall g1 g2 f a b. (Ditraversable g1 Maybe a,
                                      Ditraversable g2 Maybe a,
                                      g1 :<: f, g2 :<: f, a :< b)
              => Cxt f a b -> Maybe (Cxt (g1 :+: g2) a b)
deepProject2' (Hole x) = return $ Hole x
deepProject2' (Term t) = do
  v <- proj2 t
  v' <- dimapM deepProject2' v
  return $ Term v'

-- |A variant of 'deepProject3' where the sub signatures are required to be
-- 'Traversable rather than the whole signature.
deepProject3' :: forall g1 g2 g3 f a b. (Ditraversable g1 Maybe a,
                                         Ditraversable g2 Maybe a,
                                         Ditraversable g3 Maybe a,
                                         g1 :<: f, g2 :<: f,
                                         g3 :<: f, a :< b)
              => Cxt f a b -> Maybe (Cxt (g1 :+: g2 :+: g3) a b)
deepProject3' (Hole x) = return $ Hole x
deepProject3' (Term t) = do
  v <- proj3 t
  v' <- dimapM deepProject3' v
  return $ Term v'

{-| A variant of 'inj' for binary sum signatures.  -}
inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a b -> g a b
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

{-| A variant of 'inj' for ternary sum signatures.  -}
inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a b -> g a b
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |Inject a term where the outermost layer is a sub signature.
inject :: (g :<: f) => g a (Cxt f a b) -> Cxt f a b
inject = Term . inj

-- |Inject a term where the outermost layer is a binary sub signature.
inject2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) p (Cxt g p a) -> Cxt g p a
inject2 = Term . inj2

-- |Inject a term where the outermost layer is a ternary sub signature.
inject3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) p (Cxt g p a)
        -> Cxt g p a
inject3 = Term . inj3

-- |Inject a term over a sub signature to a term over larger signature.
deepInject :: (Difunctor g, Difunctor f, g :<: f) => Cxt g a a -> Cxt f a a
deepInject = appSigFun inj

-- |Inject a term over a binary sub signature to a term over larger signature.
deepInject2 :: (Difunctor f1, Difunctor f2, Difunctor g, f1 :<: g, f2 :<: g)
            => Cxt (f1 :+: f2) a a -> Cxt g a a
deepInject2 = appSigFun inj2

-- |Inject a term over a ternary signature to a term over larger signature.
deepInject3 :: (Difunctor f1, Difunctor f2, Difunctor f3, Difunctor g,
                f1 :<: g, f2 :<: g, f3 :<: g)
            => Cxt (f1 :+: f2 :+: f3) a a -> Cxt g a a
deepInject3 =  appSigFun inj3

injectConst :: (Difunctor g, g :<: f) => Const g -> Cxt f Nothing a
injectConst = inject . fmap (const undefined)

injectConst2 :: (Difunctor f1, Difunctor f2, Difunctor g, f1 :<: g, f2 :<: g)
             => Const (f1 :+: f2) -> Cxt g Nothing a
injectConst2 = inject2 . fmap (const undefined)

injectConst3 :: (Difunctor f1, Difunctor f2, Difunctor f3, Difunctor g,
                 f1 :<: g, f2 :<: g, f3 :<: g)
             => Const (f1 :+: f2 :+: f3) -> Cxt g Nothing a
injectConst3 = inject3 . fmap (const undefined)

projectConst :: (Difunctor g, g :<: f) => Cxt f Nothing a -> Maybe (Const g)
projectConst = fmap (fmap (const ())) . project

{-| This function injects a whole context into another context. -}
injectCxt :: (Difunctor g, g :<: f) => Cxt g p (Cxt f p a) -> Cxt f p a
injectCxt (Hole x) = x
injectCxt (Term t) = inject $ fmap injectCxt t

{-| This function lifts the given functor to a context. -}
liftCxt :: (Difunctor f, g :<: f) => g a b -> Cxt f a b
liftCxt g = simpCxt $ inj g

instance (Show (f a e), Show (g a e)) => Show ((f :+: g) a e) where
    show (Inl v) = show v
    show (Inr v) = show v

instance (Ord (f a e), Ord (g a e)) => Ord ((f :+: g) a e) where
    compare (Inl _) (Inr _) = LT
    compare (Inr _) (Inl _) = GT
    compare (Inl x) (Inl y) = compare x y
    compare (Inr x) (Inr y) = compare x y

instance (Eq (f a e), Eq (g a e)) => Eq ((f :+: g) a e) where
    (Inl x) == (Inl y) = x == y
    (Inr x) == (Inr y) = x == y                   
    _ == _ = False