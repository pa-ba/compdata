{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleInstances,
  OverlappingInstances, TypeOperators, TemplateHaskell #-}

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
-- data types, and scoped substitution. Capture-avoidance is /not/ taken into
-- account.
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
import Data.Comp.Number
import Data.Comp.Algebra
import Data.Comp.Derive
import Data.Foldable hiding (elem, notElem)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (or, foldl)

-- | This type represents substitutions of contexts, i.e. finite
-- mappings from variables to contexts.
type CxtSubst h a f v = Map v (Cxt h f a)

-- | This type represents substitutions of terms, i.e. finite mappings
-- from variables to terms.
type Subst f v = CxtSubst NoHole () f v

{-| This multiparameter class defines functors with variables. An instance
  @HasVar f v@ denotes that values over @f@ might contain and bind variables of
  type @v@. -}
class HasVars f v where
    -- | Indicates whether the @f@ constructor is a variable. The
    -- default implementation returns @Nothing@.
    isVar :: f a -> Maybe v
    isVar _ = Nothing
    
    -- | Indicates the set of variables bound by the @f@ constructor
    -- for each argument of the constructor. For example for a
    -- non-recursive let binding:
    -- @
    -- data Let e = Let Var e e
    -- instance HasVars Let Var where
    --   bindsVars (Let v x y) = Map.fromList [(y, (Set.singleton v))]
    -- @
    -- If, instead, the let binding is recursive, the methods has to
    -- be implemented like this:
    -- @
    --   bindsVars (Let v x y) = Map.fromList [(x, (Set.singleton v)),
    --                                         (y, (Set.singleton v))]
    -- @
    -- This indicates that the scope of the bound variable also
    -- extends to the right-hand side of the variable binding.
    --
    -- The default implementation returns the empty map.
    bindsVars :: Ord a => f a -> Map a (Set v)
    bindsVars _ = Map.empty


$(derive [liftSum] [''HasVars])

-- | Same as 'isVar' but it returns Nothing@ instead of @Just v@ if
-- @v@ is contained in the given set of variables.
    
isVar' :: (HasVars f v, Ord v) => Set v -> f a -> Maybe v
isVar' b t = do v <- isVar t
                if v `Set.member` b
                   then Nothing
                   else return v
   
-- | This combinator pairs every argument of a given constructor with
-- the set of (newly) bound variables according to the corresponding
-- 'HasVars' type class instance.
getBoundVars :: (HasVars f v, Traversable f) => f a -> f (Set v, a)
getBoundVars t = let n = number t
                     m = bindsVars n
                     trans x = (Map.findWithDefault Set.empty x m, unNumbered x)
                 in fmap trans n
                    
-- | This combinator combines 'getBoundVars' with the generic 'fmap' function.
fmapBoundVars :: (HasVars f v, Traversable f) => (Set v -> a -> b) -> f a -> f b
fmapBoundVars f t = let n = number t
                        m = bindsVars n
                        trans x = f (Map.findWithDefault Set.empty x m) (unNumbered x)
                    in fmap trans n                    
                    
-- | This combinator combines 'getBoundVars' with the generic 'foldl' function.   
foldlBoundVars :: (HasVars f v, Traversable f) => (b -> Set v -> a -> b) -> b -> f a -> b
foldlBoundVars f e t = let n = number t
                           m = bindsVars n
                           trans x y = f x (Map.findWithDefault Set.empty y m) (unNumbered y) 
                       in foldl trans e n

-- | Convert variables to holes, except those that are bound.
varsToHoles :: (Traversable f, HasVars f v, Ord v) => Term f -> Context f v
varsToHoles t = cata alg t Set.empty
    where alg :: (Traversable f, HasVars f v, Ord v) => Alg f (Set v -> Context f v)
          alg t vars = case isVar t of
            Just v | v `Set.member` vars -> Hole v
            _  -> Term $ fmapBoundVars run t
              where 
                run newVars f = f $ newVars `Set.union` vars

-- |Algebra for checking whether a variable is contained in a term, except those
-- that are bound.
containsVarAlg :: (Eq v, HasVars f v, Traversable f, Ord v) => v -> Alg f Bool
containsVarAlg v t = foldlBoundVars run local t
    where local = case isVar t of
                    Just v' -> v == v'
                    Nothing -> False
          run acc vars b = acc || (not (v `Set.member` vars) && b)

{-| This function checks whether a variable is contained in a context. -}
containsVar :: (Eq v, HasVars f v, Traversable f, Ord v)
            => v -> Cxt h f a -> Bool
containsVar v = free (containsVarAlg v) (const False)

-- |Algebra for generating a set of variables contained in a term, except those
-- that are bound.
variablesAlg :: (Ord v, HasVars f v, Traversable f) => Alg f (Set v)
variablesAlg t = foldlBoundVars run local t
    where local = case isVar t of
                    Just v -> Set.singleton v
                    Nothing -> Set.empty
          run acc bvars vars = acc `Set.union` (vars `Set.difference` bvars)


{-| This function computes the list of variables occurring in a context. -}
variableList :: (Ord v, HasVars f v, Traversable f) => Cxt h f a -> [v]
variableList = Set.toList . variables

{-| This function computes the set of variables occurring in a context. -}
variables :: (Ord v, HasVars f v, Traversable f) => Cxt h f a -> Set v
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

instance (Ord v, HasVars f v, Traversable f)
    => SubstVars v (Cxt h f a) (Cxt h f a) where
        -- have to use explicit GADT pattern matching!!
        -- subst f = free (substAlg f) Hole
  substVars subst = doSubst Set.empty
    where doSubst _ (Hole a) = Hole a
          doSubst b (Term t) = case isVar' b t >>= subst of 
            Just new -> new
            Nothing  -> Term $ fmapBoundVars run t
              where run vars s = doSubst (b `Set.union` vars) s

instance (SubstVars v t a, Functor f) => SubstVars v t (f a) where
    substVars f = fmap (substVars f) 

{-| This function composes two substitutions @s1@ and @s2@. That is,
applying the resulting substitution is equivalent to first applying
@s2@ and then @s1@. -}
compSubst :: (Ord v, HasVars f v, Traversable f)
          => CxtSubst h a f v -> CxtSubst h a f v -> CxtSubst h a f v
compSubst s1 s2 = fmap (appSubst s1) s2 `Map.union` s1