{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             FlexibleInstances, FlexibleContexts, EmptyDataDecls,
             GADTs, KindSignatures, TypeSynonymInstances, TypeFamilies, RankNTypes, ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Sum
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module provides the infrastructure to extend signatures.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Sum (
  (:<:)(..),
  (:+:)(..),
  project,
  deepProject,
  deepProject',
  inject,
  injectCxt,
  deepInject,
  deepInject2,
  deepInject3,
  substHoles,
  substHoles'
   ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Algebra

import Control.Applicative
import Control.Monad hiding (sequence)


import Data.Maybe
import Data.Traversable
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map


import Prelude hiding (foldr,sequence)


infixr 6 :+:


-- |Data type defining coproducts.
data (f :+: g) e = Inl (f e)
                 | Inr (g e)

instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (Inl e) = Inl (fmap f e)
    fmap f (Inr e) = Inr (fmap f e)

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
    foldr f b (Inl e) = foldr f b e
    foldr f b (Inr e) = foldr f b e

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
    traverse f (Inl e) = Inl <$> traverse f e
    traverse f (Inr e) = Inr <$> traverse f e



-- |The subsumption relation.
class sub :<: sup where
  inj :: sub a -> sup a
  proj :: sup a -> Maybe (sub a)

instance (:<:) f f where
    inj = id
    proj = Just

instance (:<:) f (f :+: g) where
    inj = Inl
    proj (Inl x) = Just x
    proj (Inr _) = Nothing

instance (f :<: g) => (:<:) f (h :+: g) where
    inj = Inr . inj
    proj (Inr x) = proj x
    proj (Inl _) = Nothing


-- |Project a sub term from a compound term.
project :: (g :<: f) => Cxt h f a -> Maybe (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = proj t

-- |Project a sub term recursively from a term.
deepProject :: (Traversable f, Functor g, g :<: f) => Cxt h f a -> Maybe (Cxt h g a)
deepProject = applySigFunM proj

-- |Project a sub term recursively from a term, but where the subterm
-- signature is required to be traversable.
deepProject' :: forall g f h a. (Traversable g, g :<: f) => Cxt h f a
             -> Maybe (Cxt h g a)
deepProject' val = do
  v <- project val
  v' <- sequence $ (fmap deepProject' v :: g (Maybe (Cxt h g a)))
  return $ inject v'

-- |Inject a term into a compound term.
inject :: (g :<: f) => g (Cxt h f a) -> Cxt h f a
inject = Term . inj


{-| This function injects a whole context into another context. -}

injectCxt :: (Functor g, g :<: f) => Cxt h' g (Cxt h f a) -> Cxt h f a
injectCxt = algHom' inject


{-| Deep injection function.  -}

deepInject  :: (Functor g, Functor f, g :<: f) => Cxt h g a -> Cxt h f a
deepInject = applySigFun inj

{-| This is a variant of 'inj' for binary sum signatures.  -}

inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a -> g a
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

-- |A recursive version of 'inj2'.
deepInject2 :: (Functor f1, Functor f2, Functor g, f1 :<: g, f2 :<: g)
            => Cxt h (f1 :+: f2) a -> Cxt h g a
deepInject2 = applySigFun inj2

{-| This is a variant of 'inj' for ternary sum signatures.  -}

inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g)
     => (f1 :+: f2 :+: f3) a -> g a
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |A recursive version of 'inj3'.
deepInject3 :: (Functor f1, Functor f2, Functor f3, Functor g, f1 :<: g, f2 :<: g, f3 :<: g)
            => Cxt h (f1 :+: f2 :+: f3) a -> Cxt h g a
deepInject3 =  applySigFun inj3


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