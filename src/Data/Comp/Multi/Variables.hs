{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleInstances,
  OverlappingInstances, TypeOperators, KindSignatures, FlexibleContexts, ScopedTypeVariables, RankNTypes, TemplateHaskell #-}
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
     CxtSubst,
     Subst,
     varsToHoles,
     containsVar,
     variables,
     variableList,
     variables',
     substVars,
     appSubst,
     compSubst
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Functor
import Data.Comp.Multi.Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe


-- type CxtSubst h a f v =  [A (v :*: (Cxt h f a))]

-- type Subst f v = CxtSubst NoHole Nothing f v

type GSubst v a = NatM Maybe (K v) a

type CxtSubst h a f v =  GSubst v (Cxt h f a)

type Subst f v = CxtSubst NoHole Nothing f v

{-| This multiparameter class defines functors with variables. An instance
  @HasVar f v@ denotes that values over @f@ might contain and bind variables of
  type @v@. -}
class HasVars (f  :: (* -> *) -> * -> *) v where
    isVar :: f a :=> Maybe v
    isVar _ = Nothing
    bindsVars :: f a :=> [v]
    bindsVars _ = []

$(derive [liftSum] [''HasVars])

instance HasVars f v => HasVars (Cxt h f) v where
    isVar (Term t) = isVar t
    isVar _ = Nothing
    bindsVars (Term t) = bindsVars t
    bindsVars _ = []

-- Auxiliary data type, used only to define varsToHoles
data C a b i = C{ unC :: a -> b i }

varsToHoles :: forall f v. (HFunctor f, HasVars f v, Eq v) =>
                Term f :-> Context f (K v)
varsToHoles t = unC (cata alg t) []
    where alg :: (HFunctor f, HasVars f v, Eq v) =>
                 Alg f (C [v] (Context f (K v)))
          alg t = C $ \vars ->
              let vars' = vars ++ bindsVars t in
              case isVar t of
                Just v ->
                    -- Check for capture-avoidance
                    if v `elem` vars' then
                        Term $ hfmap (`unC` vars') t
                    else
                        Hole $ K v
                Nothing ->
                    Term $ hfmap (`unC` vars') t

containsVarAlg :: (Eq v, HasVars f v, HFoldable f) => v -> Alg f (K Bool)
containsVarAlg v t = K $ v `notElem` bindsVars t &&
                         (local || kfoldl (||) False t)
    where local = case isVar t of
                    Just v' -> v == v'
                    Nothing -> False

{-| This function checks whether a variable is contained in a context. -}
containsVar :: (Eq v, HasVars f v, HFoldable f, HFunctor f)
            => v -> Cxt h f a :=> Bool
containsVar v = unK . free (containsVarAlg v) (const $ K False)

variableListAlg :: (HasVars f v, HFoldable f, Eq v) => Alg f (K [v])
variableListAlg t = K $ filter (`notElem` bindsVars t) $ kfoldl (++) local t
    where local = case isVar t of
                    Just v -> [v]
                    Nothing -> [] 

{-| This function computes the list of variables occurring in a context. -}
variableList :: (HasVars f v, HFoldable f, HFunctor f, Eq v)
             => Cxt h f a :=> [v]
variableList = unK . free variableListAlg (const $ K [])

variablesAlg :: (Ord v, HasVars f v, HFoldable f) => Alg f (K (Set v))
variablesAlg t = K $ Set.filter (`notElem` bindsVars t) $
                     kfoldl Set.union local t
    where local = case isVar t of
                    Just v -> Set.singleton v
                    Nothing -> Set.empty

{-| This function computes the set of variables occurring in a context. -}
variables :: (Ord v, HasVars f v, HFoldable f, HFunctor f)
            => Cxt h f a :=> Set v
variables = unK . free variablesAlg (const $ K Set.empty)

{-| This function computes the set of variables occurring in a context. -}
variables' :: (Ord v, HasVars f v, HFoldable f, HFunctor f)
            => Const f :=> Set v
variables' c =  case isVar c of
                  Nothing -> Set.empty
                  Just v -> Set.singleton v

{-| This function substitutes variables in a context according to a
partial mapping from variables to contexts.-}
class SubstVars v t a where
    substVars :: GSubst v t -> a :-> a

appSubst :: SubstVars v t a => GSubst v t -> a :-> a
appSubst = substVars

instance (Ord v, HasVars f v, HFunctor f) => SubstVars v (Cxt h f a) (Cxt h f a) where
    -- have to use explicit GADT pattern matching!!
    -- subst f = free (substAlg f) Hole
    substVars _ (Hole a) = Hole a
    substVars f (Term v) = substAlg f v
        where  substAlg :: (HasVars f v) => CxtSubst h a f v
                        -> Alg f (Cxt h f a)
               substAlg f t = fromMaybe (Term t) (isVar t >>= f . K)
    -- The code below does not work with GHC 7
    -- substVars _ (Hole a) = Hole a
    -- substVars f (Term v) = let f' = res (bindsVars v) f in
    --                         substAlg f' $ hfmap (substVars f') v
    --     where  substAlg :: (HasVars f v) => CxtSubst h a f v
    --                     -> Alg f (Cxt h f a)
    --            substAlg f t = fromMaybe (Term t) (isVar t >>= f . K)
    --            res :: Eq v => [v] -> GSubst v t -> GSubst v t
    --            res vars f x = if unK x `elem` vars then Nothing else f x

instance (SubstVars v t a, HFunctor f) => SubstVars v t (f a) where
    substVars f = hfmap (substVars f) 

{-| This function composes two substitutions @s1@ and @s2@. That is,
applying the resulting substitution is equivalent to first applying
@s2@ and then @s1@. -}

compSubst :: (Ord v, HasVars f v, HFunctor f)
          => CxtSubst h a f v -> CxtSubst h a f v -> CxtSubst h a f v
compSubst s1 s2 v = case s2 v of
                      Nothing -> s1 v
                      Just t -> Just $ appSubst s1 t