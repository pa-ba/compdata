{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleInstances,
  OverlappingInstances, TypeOperators, KindSignatures, FlexibleContexts, ScopedTypeVariables, RankNTypes #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Variables
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines an abstract notion of (bound) variables in compositional
-- data types, and capture-avoiding substitution. All definitions are
-- generalised versions of those in "Data.Comp.Variables".
--
--------------------------------------------------------------------------------
module Data.Comp.Multi.Variables
    (
     HasVars(..),
     GSubst,
     HCxtSubst,
     Subst,
     varsToHHoles,
     containsVar,
     variables,
     variableList,
     variables',
     substVars,
     appSubst,
     compSubst
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Functor
import Data.Comp.Multi.Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe


-- type HCxtSubst h a f v =  [A (v :*: (HCxt h f a))]

-- type Subst f v = HCxtSubst HNoHole HNothing f v

type GSubst v a = NatM Maybe (K v) a

type HCxtSubst h a f v =  GSubst v (HCxt h f a)

type Subst f v = HCxtSubst HNoHole HNothing f v

{-| This multiparameter class defines functors with variables. An instance
  @HasVar f v@ denotes that values over @f@ might contain and bind variables of
  type @v@. -}
class HasVars (f  :: (* -> *) -> * -> *) v where
    isVar :: f a :=> Maybe v
    isVar _ = Nothing
    bindsVars :: f a :=> [v]
    bindsVars _ = []

instance (HasVars f v, HasVars g v) => HasVars (f :++: g) v where
    isVar (HInl v) = isVar v
    isVar (HInr v) = isVar v
    bindsVars (HInl v) = bindsVars v
    bindsVars (HInr v) = bindsVars v

instance HasVars f v => HasVars (HCxt h f) v where
    isVar (HTerm t) = isVar t
    isVar _ = Nothing
    bindsVars (HTerm t) = bindsVars t
    bindsVars _ = []

-- Auxiliary data type, used only to define varsToHoles
data C a b i = C{ unC :: a -> b i }

varsToHHoles :: forall f v. (HFunctor f, HasVars f v, Eq v) =>
                HTerm f :-> HContext f (K v)
varsToHHoles t = unC (hcata alg t) []
    where alg :: (HFunctor f, HasVars f v, Eq v) =>
                 HAlg f (C [v] (HContext f (K v)))
          alg t = C $ \vars ->
              let vars' = vars ++ bindsVars t in
              case isVar t of
                Just v ->
                    -- Check for capture-avoidance
                    if v `elem` vars' then
                        HTerm $ hfmap (\x -> unC x vars') t
                    else
                        HHole $ K v
                Nothing ->
                    HTerm $ hfmap (\x -> unC x vars') t

containsVarAlg :: (Eq v, HasVars f v, HFoldable f) => v -> HAlg f (K Bool)
containsVarAlg v t = K $ v `notElem` bindsVars t &&
                         (local || kfoldl (||) False t)
    where local = case isVar t of
                    Just v' -> v == v'
                    Nothing -> False

{-| This function checks whether a variable is contained in a context. -}
containsVar :: (Eq v, HasVars f v, HFoldable f, HFunctor f)
            => v -> HCxt h f a :=> Bool
containsVar v = unK . hfree (containsVarAlg v) (const $ K False)

variableListAlg :: (HasVars f v, HFoldable f, Eq v) => HAlg f (K [v])
variableListAlg t = K $ filter (`notElem` bindsVars t) $ kfoldl (++) local t
    where local = case isVar t of
                    Just v -> [v]
                    Nothing -> [] 

{-| This function computes the list of variables occurring in a context. -}
variableList :: (HasVars f v, HFoldable f, HFunctor f, Eq v)
             => HCxt h f a :=> [v]
variableList = unK . hfree variableListAlg (const $ K [])

variablesAlg :: (Ord v, HasVars f v, HFoldable f) => HAlg f (K (Set v))
variablesAlg t = K $ Set.filter (`notElem` bindsVars t) $
                     kfoldl Set.union local t
    where local = case isVar t of
                    Just v -> Set.singleton v
                    Nothing -> Set.empty

{-| This function computes the set of variables occurring in a context. -}
variables :: (Ord v, HasVars f v, HFoldable f, HFunctor f)
            => HCxt h f a :=> Set v
variables = unK . hfree variablesAlg (const $ K Set.empty)

{-| This function computes the set of variables occurring in a context. -}
variables' :: (Ord v, HasVars f v, HFoldable f, HFunctor f)
            => HConst f :=> Set v
variables' c =  case isVar c of
                  Nothing -> Set.empty
                  Just v -> Set.singleton v

{-| This function substitutes variables in a context according to a
partial mapping from variables to contexts.-}
class SubstVars v t a where
    substVars :: GSubst v t -> a :-> a

appSubst :: SubstVars v t a => GSubst v t -> a :-> a
appSubst = substVars

instance (Ord v, HasVars f v, HFunctor f) => SubstVars v (HCxt h f a) (HCxt h f a) where
    -- have to use explicit GADT pattern matching!!
    -- subst f = hfree (substAlg f) HHole
    substVars _ (HHole a) = HHole a
    substVars f (HTerm v) = let f' = res (bindsVars v) f in
                            substAlg f' $ hfmap (substVars f') v
        where  substAlg :: (HasVars f v) => HCxtSubst h a f v
                        -> HAlg f (HCxt h f a)
               substAlg f t = fromMaybe (HTerm t) (isVar t >>= f . K)
               res :: Eq v => [v] -> GSubst v t -> GSubst v t
               res vars f x = if unK x `elem` vars then Nothing else f x

instance (SubstVars v t a, HFunctor f) => SubstVars v t (f a) where
    substVars f = hfmap (substVars f) 

{-| This function composes two substitutions @s1@ and @s2@. That is,
applying the resulting substitution is equivalent to first applying
@s2@ and then @s1@. -}

compSubst :: (Ord v, HasVars f v, HFunctor f)
          => HCxtSubst h a f v -> HCxtSubst h a f v -> HCxtSubst h a f v
compSubst s1 s2 v = case s2 v of
                      Nothing -> s1 v
                      Just t -> Just $ appSubst s1 t