{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
             ScopedTypeVariables #-}

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

module Data.Comp.Sum (
  (:<:)(..),
  (:+:)(..),
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
  inj2,
  inj3,
  inject,
  inject2,
  inject3,
  deepInject,
  deepInject2,
  deepInject3,
  deepInjectE,
  deepInjectE2,
  deepInjectE3,
  injectConst,
  injectConst2,
  injectConst3,
  projectConst,
  injectCxt,
  liftCxt,
  substHoles,
  substHoles'
   ) where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Ops
import Data.Comp.ExpFunctor

import Control.Monad hiding (sequence)
import Prelude hiding (sequence)


import Data.Maybe
import Data.Traversable
import Data.Map (Map)
import qualified Data.Map as Map

{-| A variant of 'proj' for binary sum signatures.  -}
proj2 :: forall f g1 g2 a. (g1 :<: f, g2 :<: f) => f a -> Maybe ((g1 :+: g2) a)
proj2 x = case proj x of
            Just (y :: g1 a) -> Just $ inj y
            _ -> liftM inj (proj x :: Maybe (g2 a))

{-| A variant of 'proj' for ternary sum signatures.  -}
proj3 :: forall f g1 g2 g3 a. (g1 :<: f, g2 :<: f, g3 :<: f) => f a
      -> Maybe ((g1 :+: g2 :+: g3) a)
proj3 x = case proj x of
            Just (y :: g1 a) -> Just $ inj y
            _ -> case proj x of
                   Just (y :: g2 a) -> Just $ inj y
                   _ -> liftM inj (proj x :: Maybe (g3 a))

-- |Project a sub term from a compound term.
project :: (g :<: f) => Cxt h f a -> Maybe (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = proj t

-- |Project a binary sub term from a compound term.
project2 :: (g1 :<: f, g2 :<: f) => Cxt h f a -> Maybe ((g1 :+: g2) (Cxt h f a))
project2 (Hole _) = Nothing
project2 (Term t) = proj2 t

-- |Project a ternary sub term from a compound term.
project3 :: (g1 :<: f, g2 :<: f, g3 :<: f) => Cxt h f a
         -> Maybe ((g1 :+: g2 :+: g3) (Cxt h f a))
project3 (Hole _) = Nothing
project3 (Term t) = proj3 t

-- |Project a sub term recursively from a term.
deepProject :: (Traversable f, Functor g, g :<: f) => Cxt h f a
            -> Maybe (Cxt h g a)
deepProject = appSigFunM proj

-- |Project a binary sub term recursively from a term.
deepProject2 :: (Traversable f, Functor g1, Functor g2, g1 :<: f, g2 :<: f) => Cxt h f a -> Maybe (Cxt h (g1 :+: g2) a)
deepProject2 = appSigFunM proj2

-- |Project a ternary sub term recursively from a term.
deepProject3 :: (Traversable f, Functor g1, Functor g2, Functor g3,
                 g1 :<: f, g2 :<: f, g3 :<: f) => Cxt h f a
             -> Maybe (Cxt h (g1 :+: g2 :+: g3) a)
deepProject3 = appSigFunM proj3

-- |A variant of 'deepProject' where the sub signature is required to be
-- 'Traversable' rather than the whole signature.
deepProject' :: forall g f h a. (Traversable g, g :<: f) => Cxt h f a
             -> Maybe (Cxt h g a)
deepProject' val = do
  v <- project val
  v' <- sequence (fmap deepProject' v :: g (Maybe (Cxt h g a)))
  return $ Term v'

-- |A variant of 'deepProject2' where the sub signatures are required to be
-- 'Traversable' rather than the whole signature.
deepProject2' :: forall g1 g2 f h a. (Traversable g1, Traversable g2,
                                      g1 :<: f, g2 :<: f) => Cxt h f a
             -> Maybe (Cxt h (g1 :+: g2) a)
deepProject2' val = do
  v <- project2 val
  v' <- sequence (fmap deepProject2' v :: (g1 :+: g2) (Maybe (Cxt h (g1 :+: g2) a)))
  return $ Term v'

-- |A variant of 'deepProject3' where the sub signatures are required to be
-- 'Traversable' rather than the whole signature.
deepProject3' :: forall g1 g2 g3 f h a. (Traversable g1, Traversable g2,
                                         Traversable g3, g1 :<: f, g2 :<: f,
                                         g3 :<: f) => Cxt h f a
             -> Maybe (Cxt h (g1 :+: g2 :+: g3) a)
deepProject3' val = do
  v <- project3 val
  v' <- sequence (fmap deepProject3' v :: (g1 :+: g2 :+: g3) (Maybe (Cxt h (g1 :+: g2 :+: g3) a)))
  return $ Term v'

{-| A variant of 'inj' for binary sum signatures.  -}
inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a -> g a
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

{-| A variant of 'inj' for ternary sum signatures.  -}
inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a -> g a
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |Inject a term into a compound term.
inject :: (g :<: f) => g (Cxt h f a) -> Cxt h f a
inject = Term . inj

-- |Inject a term into a binary compound term.
inject2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) (Cxt h g a) -> Cxt h g a
inject2 = Term . inj2

-- |Inject a term into a ternary compound term.
inject3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) (Cxt h g a) -> Cxt h g a
inject3 = Term . inj3

-- |A recursive version of 'inj'.
deepInject  :: (Functor g, Functor f, g :<: f) => Cxt h g a -> Cxt h f a
deepInject = appSigFun inj

-- |A recursive version of 'inj2'.
deepInject2 :: (Functor f1, Functor f2, Functor g, f1 :<: g, f2 :<: g)
            => Cxt h (f1 :+: f2) a -> Cxt h g a
deepInject2 = appSigFun inj2

-- |A recursive version of 'inj3'.
deepInject3 :: (Functor f1, Functor f2, Functor f3, Functor g,
                f1 :<: g, f2 :<: g, f3 :<: g)
            => Cxt h (f1 :+: f2 :+: f3) a -> Cxt h g a
deepInject3 =  appSigFun inj3

{-| A variant of 'deepInject' for exponential signatures. -}
deepInjectE :: (ExpFunctor g, g :<: f) => Term g -> Term f
deepInjectE = cataE inject

{-| A variant of 'deepInject2' for exponential signatures. -}
deepInjectE2 :: (ExpFunctor g1, ExpFunctor g2, g1 :<: f, g2 :<: f) =>
                Term (g1 :+: g2)
             -> Term f
deepInjectE2 = cataE inject2

{-| A variant of 'deepInject3' for exponential signatures. -}
deepInjectE3 :: (ExpFunctor g1, ExpFunctor g2, ExpFunctor g3,
                 g1 :<: f, g2 :<: f, g3 :<: f) =>
                Term (g1 :+: g2 :+: g3)
             -> Term f
deepInjectE3 = cataE inject3

injectConst :: (Functor g, g :<: f) => Const g -> Cxt h f a
injectConst = inject . fmap (const undefined)

injectConst2 :: (Functor f1, Functor f2, Functor g, f1 :<: g, f2 :<: g)
             => Const (f1 :+: f2) -> Cxt h g a
injectConst2 = inject2 . fmap (const undefined)

injectConst3 :: (Functor f1, Functor f2, Functor f3, Functor g, f1 :<: g, f2 :<: g, f3 :<: g)
             => Const (f1 :+: f2 :+: f3) -> Cxt h g a
injectConst3 = inject3 . fmap (const undefined)

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

instance (Functor f) => Monad (Context f) where
    return = Hole
    (>>=) = substHoles


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