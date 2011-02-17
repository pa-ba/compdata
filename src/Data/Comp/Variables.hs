{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleInstances,
  OverlappingInstances, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Variables
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines an abstraction notion of a variable in compositional
-- data type.
--
--------------------------------------------------------------------------------
module Data.Comp.Variables (
  HasVars(..),
  Subst,
  CxtSubst,
  varsToHoles,
  containsVar,
  variables,
  variableList,
  variables',
  substVars,
  appSubst,
  compSubst) where

import Data.Comp.Term
import Data.Comp.Sum
import Data.Comp.Algebra
import Data.Foldable

import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Prelude hiding (or, foldl)

type CxtSubst h a f v = Map v (Cxt h f a)

type Subst f v = CxtSubst NoHole Nothing f v

{-| This multiparameter class defines functors with variables. An
instance @HasVar f v@ denotes that values over @f@ might contain
variables of type @v@. -}

class HasVars f v where
    isVar :: f a -> Maybe v
    isVar _ = Nothing

instance (HasVars f v, HasVars g v) => HasVars (f :+: g) v where
    isVar (Inl v) = isVar v
    isVar (Inr v) = isVar v

instance HasVars f v => HasVars (Cxt h f) v where
    isVar (Term t) = isVar t
    isVar _ = Nothing

varsToHoles :: (Functor f, HasVars f v) => Term f -> Context f v
varsToHoles = cata alg
    where alg t = case isVar t of 
                    Just v -> Hole v
                    Nothing -> Term t

containsVarAlg :: (Eq v, HasVars f v, Foldable f) => v -> Alg f Bool
containsVarAlg v t = local || or t 
    where local = case isVar t of
                    Just v' -> v == v'
                    Nothing -> False

{-| This function checks whether a variable is contained in a
context. -}

containsVar :: (Eq v, HasVars f v, Foldable f, Functor f)
            => v -> Cxt h f a -> Bool
containsVar v = free (containsVarAlg v) (const False)

variablesAlg :: (Ord v, HasVars f v, Foldable f)
            => Alg f (Set v)
variablesAlg t = foldl Set.union local t
    where local = case isVar t of
                    Just v -> Set.singleton v
                    Nothing -> Set.empty

variableListAlg :: (Ord v, HasVars f v, Foldable f)
            => Alg f [v]
variableListAlg t = foldl (++) local t
    where local = case isVar t of
                    Just v -> [v]
                    Nothing -> [] 

{-| This function computes the list of variables occurring in a
context. -}

variableList :: (Ord v, HasVars f v, Foldable f, Functor f)
            => Cxt h f a -> [v]
variableList = free variableListAlg (const [])

{-| This function computes the set of variables occurring in a
context. -}

variables :: (Ord v, HasVars f v, Foldable f, Functor f)
            => Cxt h f a -> Set v
variables = free variablesAlg (const Set.empty)

{-| This function computes the set of variables occurring in a
context. -}

variables' :: (Ord v, HasVars f v, Foldable f, Functor f)
            => Const f -> Set v
variables' c =  case isVar c of
                  Nothing -> Set.empty
                  Just v -> Set.singleton v


substAlg :: (HasVars f v) => (v -> Maybe (Cxt h f a)) -> Alg f (Cxt h f a)
substAlg f t = fromMaybe (Term t) (isVar t >>= f)

{-| This function substitutes variables in a context according to a
partial mapping from variables to contexts.-}



class SubstVars v t a where
    substVars :: (v -> Maybe t) -> a -> a


appSubst :: (Ord v, SubstVars v t a) => Map v t -> a -> a
appSubst subst = substVars f
    where f v = Map.lookup v subst

instance (Ord v, HasVars f v, Functor f) => SubstVars v (Cxt h f a) (Cxt h f a) where
    substVars f (Term v) = substAlg f $ fmap (substVars f) v
    substVars _ (Hole a) = Hole a
-- have to use explicit GADT pattern matching!!
-- subst f = free (substAlg f) Hole

instance (SubstVars v t a, Functor f) => SubstVars v t (f a) where
    substVars f = fmap (substVars f) 



{-| This function composes two substitutions @s1@ and @s2@. That is,
applying the resulting substitution is equivalent to first applying
@s2@ and then @s1@. -}

compSubst :: (Ord v, HasVars f v, Functor f)
          => CxtSubst h a f v -> CxtSubst h a f v -> CxtSubst h a f v
compSubst s1 s2 = fmap (appSubst s1) s2 `Map.union` s1