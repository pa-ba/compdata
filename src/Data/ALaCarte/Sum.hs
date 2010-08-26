{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             FlexibleInstances, FlexibleContexts, EmptyDataDecls,
             GADTs, KindSignatures, TypeSynonymInstances, TypeFamilies#-}

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
  NilF,
  (:<:)(..),
  (:+:)(..),
  (:++:),
  project,
  deepProject,
  inject,
  injectCxt,
  deepInject,
  substHoles,
  substHoles'
   ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Algebra

import Control.Applicative
import Control.Monad

import Data.Maybe
import Data.Traversable
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map


import Prelude hiding (foldr)


infixr 6 :+:
infixr 5 :++:

data NilF :: * -> * 


type family (:++:) (f :: * -> *) (g :: * -> *) :: * -> *

type instance (:++:) NilF f = f
type instance (:++:) (f :+: f') g = f :+: (f' :++: g)

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

instance Functor NilF where
    fmap = undefined


instance Foldable NilF where

instance Traversable NilF where


class Elem f g where
  inj' :: f a -> g a
  proj' :: g a -> Maybe (f a)

instance Elem f (f :+: g) where
    inj' = Inl
    proj' (Inl v) = Just v
    proj' (Inr _) = Nothing

instance (Elem f g) => Elem f (f' :+: g) where
    inj' = Inr . inj'
    proj' (Inl _) = Nothing
    proj' (Inr v) = proj' v

-- |The subsumption relation.
class sub :<: sup where
  inj :: sub a -> sup a
  proj :: sup a -> Maybe (sub a)

instance (:<:) f f where
    inj = id
    proj = Just
                                    
instance (:<:) NilF f where
    inj = undefined
    proj _ = undefined

instance (Elem f g, f' :<: g) => (:<:) (f :+: f') g where
  inj (Inl v) = inj' v
  inj (Inr v) = inj v

  proj v = (Inl <$> proj' v) `mplus` (Inr <$> proj v)

-- |Project a sub term from a compound term.
project :: (g :<: f) => Cxt h f a -> Maybe (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = proj t

-- |Project a sub term recursively from a term.
deepProject :: (Traversable f, Functor g, g :<: f) => Cxt h f a -> Maybe (Cxt h g a)
deepProject = applySigFunM proj

-- |Inject a term into a compound term.
inject :: (g :<: f) => g (Cxt h f a) -> Cxt h f a
inject = Term . inj


{-| This function injects a whole context into another context. -}

injectCxt :: (Functor g, g :<: f) => Cxt h' g (Cxt h f a) -> Cxt h f a
injectCxt = algHom' inject


{-| Deep injection function.  -}

deepInject  :: (Functor g, Functor f, g :<: f) => Cxt h g a -> Cxt h f a
deepInject = applySigFun inj




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