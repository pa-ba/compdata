{-# LANGUAGE MultiParamTypeClasses, RankNTypes, GADTs #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Variables
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines an abstraction notion of a variable in an a la
-- carte term.
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Variables (
  HasVars,
  containsVar,
  variables,
  substVars,
  substVars',
  applySubst,
  applySubst'                   ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Algebra
import Data.ALaCarte.Sum
import Data.Foldable

import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Prelude hiding (or, foldl)


{-| This multiparameter class defines functors with variables. An
instance @HasVar f v@ denotes that values over @f@ might contain
variables of type @v@. -}

class HasVars f v where
    isVar :: f a -> Maybe v

containsVarAlg :: (Eq v, HasVars f v, Foldable f) => v -> Alg f Bool
containsVarAlg v t = local || or t 
    where local = case isVar t of
                    Just v' -> v == v'
                    Nothing -> False

{-| This function checks whether a variable is contained in a
context. -}

containsVar :: (Eq v, HasVars f v, Foldable f, Functor f)
            => v -> Cxt h f a -> Bool
containsVar v = freeAlgHom (containsVarAlg v) (const False)

variablesAlg :: (Ord v, HasVars f v, Foldable f)
            => Alg f (Set v)
variablesAlg t = foldl Set.union local t
    where local = case isVar t of
                    Just v -> Set.singleton v
                    Nothing -> Set.empty 

{-| This function computes the set of variables occurring in a
context. -}

variables :: (Ord v, HasVars f v, Foldable f, Functor f)
            => Cxt h f a -> Set v
variables = freeAlgHom variablesAlg (const Set.empty)


substAlg :: (HasVars f v, f :<: g) => (v -> Maybe (Cxt h g a)) -> Alg f (Cxt h g a)
substAlg f t = fromMaybe (inject t) (isVar t >>= f)

{-| This function substitutes variables in a context according to a
partial mapping from variables to contexts.-}

substVars :: (HasVars f v, Functor f, f :<: g)
      => (v -> Maybe (Cxt h g a)) -> Cxt h f a -> Cxt h g a
substVars f (Term v) = substAlg f $ fmap (substVars f) v
substVars _ (Hole a) = Hole a
-- have to use explicit GADT pattern matching!!
-- subst f = freeAlgHom (substAlg f) Hole

{-| This is a slightly more general variant of 'substVars'. -}

substVars'  :: (HasVars f1 v, Functor f1, Functor f2, Functor g, f1 :<: g, f2 :<: g)
            => (v -> Maybe (Cxt h f2 a)) -> Cxt h f1 a -> Cxt h g a
substVars' f = substVars (fmap deepInject . f)

{-| This function applies a substitution (in the form of a finite
mapping) to a context. -}

applySubst :: (Ord k, HasVars f k, Functor f, f :<: g)
           => Map k (Cxt h g a) -> Cxt h f a -> Cxt h g a
applySubst subst = substVars f
    where f v = Map.lookup v subst

{-| This is a slightly more general version of 'applySubst'. -}

applySubst' :: (Ord k, HasVars f1 k,Functor f1, Functor f2, Functor g, f1 :<: g, f2 :<: g)
            => Map k (Cxt h f2 a) -> Cxt h f1 a -> Cxt h g a
applySubst' subst = applySubst (fmap deepInject subst)