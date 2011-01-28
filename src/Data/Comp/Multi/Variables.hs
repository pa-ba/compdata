{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleInstances,
  OverlappingInstances, TypeOperators, KindSignatures, FlexibleContexts, ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Variables
-- Copyright   :  3gERP, 2011
-- License     :  AllRightsReserved
-- Maintainer  :  Patrick Bahr, Tom Hvitved
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines an abstraction notion of a variable in a term.
--
--------------------------------------------------------------------------------
module Data.Comp.Multi.Variables  where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor


import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)

type CxtSubst h a f v i = Map v (Cxt h f a i)

type Subst f v i = CxtSubst NoHole Nothing f v i

{-| This multiparameter class defines functors with variables. An
instance @HasVar f v@ denotes that values over @f@ might contain
variables of type @v@. -}

class HasVars (f  :: (* -> *) -> * -> *) v where
    isVar :: (f a) :=> Maybe v
    isVar _ = Nothing

instance (HasVars f v, HasVars g v) => HasVars (f :++: g) v where
    isVar (HInl v) = isVar v
    isVar (HInr v) = isVar v

instance HasVars f v => HasVars (Cxt h f) v where
    isVar (Term t) = isVar t
    isVar _ = Nothing

varsToHoles :: forall f v. (HFunctor f, HasVars f v) => Term f :-> Context f (K v)
varsToHoles = cata alg
    where alg :: Alg f (Context f (K v))
          alg t = case isVar t of 
                    Just v -> Hole $ K v
                    Nothing -> Term t

containsVarAlg :: (Eq v, HasVars f v, HFoldable f) => v -> Alg f (K Bool)
containsVarAlg v t = K $ local || kfoldl (||) False t 
    where local = case isVar t of
                    Just v' -> v == v'
                    Nothing -> False

{-| This function checks whether a variable is contained in a
context. -}

containsVar :: (Eq v, HasVars f v, HFoldable f, HFunctor f)
            => v -> Cxt h f a :=> Bool
containsVar v = unK . freeAlgHom (containsVarAlg v) (const $ K False)


variableListAlg :: (HasVars f v, HFoldable f)
            => Alg f (K [v])
variableListAlg t = K $ kfoldl (++) local t
    where local = case isVar t of
                    Just v -> [v]
                    Nothing -> [] 

{-| This function computes the list of variables occurring in a
context. -}

variableList :: (HasVars f v, HFoldable f, HFunctor f)
            => Cxt h f a :=> [v]
variableList = unK . freeAlgHom variableListAlg (const $ K [])



variablesAlg :: (Ord v, HasVars f v, HFoldable f)
            => Alg f (K (Set v))
variablesAlg t = K $ kfoldl Set.union local t
    where local = case isVar t of
                    Just v -> Set.singleton v
                    Nothing -> Set.empty

{-| This function computes the set of variables occurring in a
context. -}

variables :: (Ord v, HasVars f v, HFoldable f, HFunctor f)
            => Cxt h f a :=> Set v
variables = unK . freeAlgHom variablesAlg (const $ K Set.empty)

{-| This function computes the set of variables occurring in a
context. -}

variables' :: (Ord v, HasVars f v, HFoldable f, HFunctor f)
            => Const f :=> Set v
variables' c =  case isVar c of
                  Nothing -> Set.empty
                  Just v -> Set.singleton v


-- substAlg :: (HasVars f v) => (NatM Maybe v (Cxt h f a)) -> Alg f (Cxt h f a)
-- substAlg f t = fromMaybe (Term t) (isVar t >>= f)

-- {-| This function substitutes variables in a context according to a
-- partial mapping from variables to contexts.-}



-- class SubstVars v t (a :: * -> *) where
--     substVars :: (v -> Maybe t) -> a :-> a


-- applySubst :: (Ord v, SubstVars v t a) => Map v t -> a :-> a
-- applySubst subst = substVars f
--     where f v = Map.lookup v subst

-- instance (Ord v, HasVars f v, HFunctor f) => SubstVars v (Cxt h f a) (Cxt h f a) where
--     substVars f (Term v) = substAlg f $ fmap (substVars f) v
--     substVars _ (Hole a) = Hole a
-- -- have to use explicit GADT pattern matching!!
-- -- subst f = freeAlgHom (substAlg f) Hole

-- instance (SubstVars v t a, HFunctor f) => SubstVars v t (f a) where
--     substVars f = fmap (substVars f) 



-- {-| This function composes two substitutions @s1@ and @s2@. That is,
-- applying the resulting substitution is equivalent to first applying
-- @s2@ and then @s1@. -}

-- compSubst :: (Ord v, HasVars f v, HFunctor f)
--           => CxtSubst h a f v -> CxtSubst h a f v -> CxtSubst h a f v
-- compSubst s1 s2 = fmap (applySubst s1) s2 `Map.union` s1