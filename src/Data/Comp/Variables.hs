{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleInstances,
  OverlappingInstances, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Variables
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk> and Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines an abstract notion of (bound) variables in compositional
-- data types, and capture-avoiding substitution.
--
--------------------------------------------------------------------------------
module Data.Comp.Variables
    (
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
     compSubst
    ) where

import Data.Comp.Term
import Data.Comp.Sum
import Data.Comp.Algebra
import Data.Foldable hiding (elem, notElem)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (or, foldl)

type CxtSubst h a f v = Map v (Cxt h f a)

type Subst f v = CxtSubst NoHole Nothing f v

{-| This multiparameter class defines functors with variables. An instance
  @HasVar f v@ denotes that values over @f@ might contain and bind variables of
  type @v@. -}
class HasVars f v where
    -- |Indicates whether the @f@ constructor is a variable.
    isVar :: f a -> Maybe v
    isVar _ = Nothing
    -- |Indicates the set of variables bound by the @f@ constructor.
    bindsVars :: f a -> [v]
    bindsVars _ = []

instance (HasVars f v, HasVars g v) => HasVars (f :+: g) v where
    isVar (Inl v) = isVar v
    isVar (Inr v) = isVar v
    bindsVars (Inl v) = bindsVars v
    bindsVars (Inr v) = bindsVars v

instance HasVars f v => HasVars (Cxt h f) v where
    isVar (Term t) = isVar t
    isVar _ = Nothing
    bindsVars (Term t) = bindsVars t
    bindsVars _ = []

-- |Convert variables to holes, except those that are bound.
varsToHoles :: (Functor f, HasVars f v, Eq v) => Term f -> Context f v
varsToHoles (Term t) = run [] t
    where run vars t =
              let vars' = vars ++ bindsVars t in
              case isVar t of
                Just v ->
                    -- Check for capture-avoidance
                    if v `elem` vars' then
                        Term $ fmap (run vars' . unTerm) t
                    else
                        Hole v
                Nothing ->
                    Term $ fmap (run vars' . unTerm) t

-- |Algebra for checking whether a variable is contained in a term, except those
-- that are bound.
containsVarAlg :: (Eq v, HasVars f v, Foldable f) => v -> Alg f Bool
containsVarAlg v t = v `notElem` bindsVars t && (local || or t)
    where local = case isVar t of
                    Just v' -> v == v'
                    Nothing -> False

{-| This function checks whether a variable is contained in a context. -}
containsVar :: (Eq v, HasVars f v, Foldable f, Functor f)
            => v -> Cxt h f a -> Bool
containsVar v = free (containsVarAlg v) (const False)

-- |Algebra for generating a set of variables contained in a term, except those
-- that are bound.
variablesAlg :: (Ord v, HasVars f v, Foldable f) => Alg f (Set v)
variablesAlg t = Set.filter (`notElem` bindsVars t) $ foldl Set.union local t
    where local = case isVar t of
                    Just v -> Set.singleton v
                    Nothing -> Set.empty

-- |Algebra for generating a list of variables contained in a term, except those
-- that are bound.
variableListAlg :: (Ord v, HasVars f v, Foldable f) => Alg f [v]
variableListAlg t = filter (`notElem` bindsVars t) $ foldl (++) local t
    where local = case isVar t of
                    Just v -> [v]
                    Nothing -> [] 

{-| This function computes the list of variables occurring in a context. -}
variableList :: (Ord v, HasVars f v, Foldable f, Functor f) => Cxt h f a -> [v]
variableList = free variableListAlg (const [])

{-| This function computes the set of variables occurring in a context. -}
variables :: (Ord v, HasVars f v, Foldable f, Functor f) => Cxt h f a -> Set v
variables = free variablesAlg (const Set.empty)

{-| This function computes the set of variables occurring in a constant. -}
variables' :: (Ord v, HasVars f v, Foldable f, Functor f) => Const f -> Set v
variables' c = case isVar c of
                 Nothing -> Set.empty
                 Just v -> Set.singleton v

{-| This multiparameter class defines substitution of values of type @t@ for
  variables of type @v@ in values of type @a@. -}
class SubstVars v t a where
    substVars :: (v -> Maybe t) -> a -> a

-- |Apply the given substitution.
appSubst :: (Ord v, SubstVars v t a) => Map v t -> a -> a
appSubst subst = substVars f
    where f v = Map.lookup v subst

instance (Ord v, HasVars f v, Functor f)
    => SubstVars v (Cxt h f a) (Cxt h f a) where
        -- have to use explicit GADT pattern matching!!
        -- subst f = free (substAlg f) Hole
    substVars _ (Hole a) = Hole a
    substVars f (Term v) = let f' = res (bindsVars v) f in
                           substAlg f' $ fmap (substVars f') v
            where substAlg :: (HasVars f v) => (v -> Maybe (Cxt h f a))
                           -> Alg f (Cxt h f a)
                  substAlg f t = fromMaybe (Term t) (isVar t >>= f)
                  res :: Eq v => [v] -> (v -> Maybe t) -> (v -> Maybe t)
                  res vars f x = if x `elem` vars then Nothing else f x

instance (SubstVars v t a, Functor f) => SubstVars v t (f a) where
    substVars f = fmap (substVars f) 

{-| This function composes two substitutions @s1@ and @s2@. That is,
applying the resulting substitution is equivalent to first applying
@s2@ and then @s1@. -}
compSubst :: (Ord v, HasVars f v, Functor f)
          => CxtSubst h a f v -> CxtSubst h a f v -> CxtSubst h a f v
compSubst s1 s2 = fmap (appSubst s1) s2 `Map.union` s1