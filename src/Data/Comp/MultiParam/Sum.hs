{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
  FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
  ScopedTypeVariables #-}
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
     liftCxt
    ) where

import Prelude hiding (sequence)
import Control.Monad hiding (sequence)
import Data.Comp.Multi.Functor (hfmap)
import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.Algebra
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.HDitraversable

{-| A variant of 'proj' for binary sum signatures.  -}
proj2 :: forall f g1 g2 a b i. (g1 :<: f, g2 :<: f) => f a b i
      -> Maybe ((g1 :+: g2) a b i)
proj2 x = case proj x of
            Just (y :: g1 a b i) -> Just $ inj y
            _ -> liftM inj (proj x :: Maybe (g2 a b i))

{-| A variant of 'proj' for ternary sum signatures.  -}
proj3 :: forall f g1 g2 g3 a b i. (g1 :<: f, g2 :<: f, g3 :<: f) => f a b i
      -> Maybe ((g1 :+: g2 :+: g3) a b i)
proj3 x = case proj x of
            Just (y :: g1 a b i) -> Just $ inj y
            _ -> case proj x of
                   Just (y :: g2 a b i) -> Just $ inj y
                   _ -> liftM inj (proj x :: Maybe (g3 a b i))

-- |Project the outermost layer of a term to a sub signature.
project :: (g :<: f) => NatM Maybe (Cxt h f a b) (g a (Cxt h f a b))
project (Term t) = proj t
project (Hole _) = Nothing
project (Place _) = Nothing

-- |Project the outermost layer of a term to a binary sub signature.
project2 :: (g1 :<: f, g2 :<: f)
            => NatM Maybe (Cxt h f a b) ((g1 :+: g2) a (Cxt h f a b))
project2 (Term t) = proj2 t
project2 (Hole _) = Nothing
project2 (Place _) = Nothing

-- |Project the outermost layer of a term to a ternary sub signature.
project3 :: (g1 :<: f, g2 :<: f, g3 :<: f)
            => NatM Maybe (Cxt h f a b) ((g1 :+: g2 :+: g3) a (Cxt h f a b))
project3 (Term t) = proj3 t
project3 (Hole _) = Nothing
project3 (Place _) = Nothing

-- |Project a term to a term over a sub signature.
deepProject :: (HDitraversable f Maybe a, HDifunctor g, g :<: f)
               => NatM Maybe (Cxt h f a b) (Cxt h g a b)
deepProject = appSigFunM proj

-- |Project a term to a term over a binary sub signature.
deepProject2 :: (HDitraversable f Maybe a, HDifunctor g1, HDifunctor g2,
                 g1 :<: f, g2 :<: f)
                => NatM Maybe (Cxt h f a b) (Cxt h (g1 :+: g2) a b)
deepProject2 = appSigFunM proj2

-- |Project a term to a term over a ternary sub signature.
deepProject3 :: (HDitraversable f Maybe a, HDifunctor g1, HDifunctor g2,
                 HDifunctor g3, g1 :<: f, g2 :<: f, g3 :<: f)
                => NatM Maybe (Cxt h f a b) (Cxt h (g1 :+: g2 :+: g3) a b)
deepProject3 = appSigFunM proj3

-- |A variant of 'deepProject' where the sub signature is required to be
-- 'Traversable rather than the whole signature.
deepProject' :: forall h g f a b. (HDitraversable g Maybe a, g :<: f)
                => NatM Maybe (Cxt h f a b) (Cxt h g a b)
deepProject' (Term t) = do
  v <- proj t
  v' <- hdimapM deepProject' v
  return $ Term v'
deepProject' (Hole x) = return $ Hole x
deepProject' (Place p) = return $ Place p

-- |A variant of 'deepProject2' where the sub signatures are required to be
-- 'Traversable rather than the whole signature.
deepProject2' :: forall h g1 g2 f a b. (HDitraversable g1 Maybe a,
                                       HDitraversable g2 Maybe a,
                                       g1 :<: f, g2 :<: f)
                 => NatM Maybe (Cxt h f a b) (Cxt h (g1 :+: g2) a b)
deepProject2' (Term t) = do
  v <- proj2 t
  v' <- hdimapM deepProject2' v
  return $ Term v'
deepProject2' (Hole x) = return $ Hole x
deepProject2' (Place p) = return $ Place p

-- |A variant of 'deepProject3' where the sub signatures are required to be
-- 'Traversable rather than the whole signature.
deepProject3' :: forall h g1 g2 g3 f a b. (HDitraversable g1 Maybe a,
                                          HDitraversable g2 Maybe a,
                                          HDitraversable g3 Maybe a,
                                          g1 :<: f, g2 :<: f, g3 :<: f)
                 => NatM Maybe (Cxt h f a b) (Cxt h (g1 :+: g2 :+: g3) a b)
deepProject3' (Term t) = do
  v <- proj3 t
  v' <- hdimapM deepProject3' v
  return $ Term v'
deepProject3' (Hole x) = return $ Hole x
deepProject3' (Place p) = return $ Place p

{-| A variant of 'inj' for binary sum signatures.  -}
inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a b :-> g a b
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

{-| A variant of 'inj' for ternary sum signatures.  -}
inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a b :-> g a b
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |Inject a term where the outermost layer is a sub signature.
inject :: (g :<: f) => g a (Cxt h f a b) :-> Cxt h f a b
inject = Term . inj

-- |Inject a term where the outermost layer is a binary sub signature.
inject2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a (Cxt h g a b) :-> Cxt h g a b
inject2 = Term . inj2

-- |Inject a term where the outermost layer is a ternary sub signature.
inject3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a (Cxt h g a b)
        :-> Cxt h g a b
inject3 = Term . inj3

-- |Inject a term over a sub signature to a term over larger signature.
deepInject :: (HDifunctor g, HDifunctor f, g :<: f)
              => Cxt h g a b :-> Cxt h f a b
deepInject = appSigFun inj

-- |Inject a term over a binary sub signature to a term over larger signature.
deepInject2 :: (HDifunctor f1, HDifunctor f2, HDifunctor g, f1 :<: g, f2 :<: g)
               => Cxt h (f1 :+: f2) a b :-> Cxt h g a b
deepInject2 = appSigFun inj2

-- |Inject a term over a ternary signature to a term over larger signature.
deepInject3 :: (HDifunctor f1, HDifunctor f2, HDifunctor f3, HDifunctor g,
                f1 :<: g, f2 :<: g, f3 :<: g)
               => Cxt h (f1 :+: f2 :+: f3) a b :-> Cxt h g a b
deepInject3 =  appSigFun inj3

injectConst :: (HDifunctor g, g :<: f) => Const g :-> Cxt h f Any a
injectConst = inject . hfmap (const undefined)

injectConst2 :: (HDifunctor f1, HDifunctor f2, HDifunctor g, f1 :<: g, f2 :<: g)
                => Const (f1 :+: f2) :-> Cxt h g Any a
injectConst2 = inject2 . hfmap (const undefined)

injectConst3 :: (HDifunctor f1, HDifunctor f2, HDifunctor f3, HDifunctor g,
                 f1 :<: g, f2 :<: g, f3 :<: g)
                => Const (f1 :+: f2 :+: f3) :-> Cxt h g Any a
injectConst3 = inject3 . hfmap (const undefined)

projectConst :: (HDifunctor g, g :<: f) => NatM Maybe (Cxt h f Any a) (Const g)
projectConst = fmap (hfmap (const (K ()))) . project

{-| This function injects a whole context into another context. -}
injectCxt :: (HDifunctor g, g :<: f) => Cxt h g a (Cxt h f a b) :-> Cxt h f a b
injectCxt (Term t) = inject $ hfmap injectCxt t
injectCxt (Hole x) = x
injectCxt (Place p) = Place p

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