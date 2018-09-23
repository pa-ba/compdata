{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Unification
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements a simple unification algorithm using compositional
-- data types.
--
--------------------------------------------------------------------------------

module Data.Comp.Unification where

import Data.Comp.Decompose
import Data.Comp.Term
import Data.Comp.Variables

import Control.Monad.Except
import Control.Monad.State

import qualified Data.Map as Map

{-| This type represents equations between terms over a specific
signature. -}

type Equation f = (Term f,Term f)

{-| This type represents list of equations. -}

type Equations f = [Equation f]

{-| This type represents errors that might occur during the
unification.  -}

data UnifError f v = FailedOccursCheck v (Term f)
                   | HeadSymbolMismatch (Term f) (Term f)
                   | UnifError String

-- | This is used in order to signal a failed occurs check during
-- unification.
failedOccursCheck :: (MonadError (UnifError f v) m) => v -> Term f -> m a
failedOccursCheck v t = throwError $ FailedOccursCheck v t

-- | This is used in order to signal a head symbol mismatch during
-- unification.
headSymbolMismatch :: (MonadError (UnifError f v) m) => Term f -> Term f -> m a
headSymbolMismatch f g = throwError $ HeadSymbolMismatch f g

-- | This function applies a substitution to each term in a list of
-- equations.
appSubstEq :: (Ord v,  HasVars f v, Traversable f) =>
     Subst f v -> Equation f -> Equation f
appSubstEq s (t1,t2) = (appSubst s t1,appSubst s t2)


{-| This function returns the most general unifier of the given
equations using the algorithm of Martelli and Montanari. -}

unify :: (MonadError (UnifError f v) m, Decompose f v, Ord v, Eq (Const f), Traversable f)
      => Equations f -> m (Subst f v)
unify = runUnifyM runUnify

-- | This type represents the state for the unification algorithm.
data UnifyState f v = UnifyState {usEqs ::Equations f, usSubst :: Subst f v}

-- | This is the unification monad that is used to run the unification
-- algorithm.
type UnifyM f v m a = StateT (UnifyState f v) m a

-- | This function runs a unification monad with the given initial
-- list of equations.
runUnifyM :: MonadError (UnifError f v) m
          => UnifyM f v m a -> Equations f -> m (Subst f v)
runUnifyM m eqs = liftM (usSubst . snd) $
                           runStateT m UnifyState { usEqs = eqs, usSubst = Map.empty}

withNextEq :: Monad m
           => (Equation f -> UnifyM f v m ()) -> UnifyM f v m ()
withNextEq m = do eqs <- gets usEqs
                  case eqs of
                    [] -> return ()
                    x : xs -> modify (\s -> s {usEqs = xs})
                           >> m x

putEqs :: Monad m
       => Equations f -> UnifyM f v m ()
putEqs eqs = modify addEqs
    where addEqs s = s {usEqs = eqs ++ usEqs s}

putBinding :: (Monad m, Ord v, HasVars f v, Traversable f) => (v, Term f) -> UnifyM f v m ()
putBinding bind = modify appSubst
    where binds = Map.fromList [bind]
          appSubst s = s { usEqs = map (appSubstEq binds) (usEqs s),
                             usSubst = compSubst binds (usSubst s)}


runUnify :: (MonadError (UnifError f v) m, Decompose f v, Ord v, Eq (Const f), Traversable f)
         => UnifyM f v m ()
runUnify = withNextEq (\ e -> unifyStep e >> runUnify)

unifyStep :: (MonadError (UnifError f v) m, Decompose f v, Ord v, Eq (Const f), Traversable f)
          => Equation f -> UnifyM f v m ()
unifyStep (s,t) = case decompose s of
                    Var v1 -> case decompose t of
                                 Var v2 -> unless (v1 == v2) $
                                             putBinding (v1, t)
                                 _ -> if containsVar v1 t
                                      then failedOccursCheck v1 t
                                      else putBinding (v1,t)
                    Fun s1 args1 -> case decompose t of
                                       Var v -> if containsVar v s
                                                 then failedOccursCheck v s
                                                 else putBinding (v,s)
                                       Fun s2 args2 -> if s1 == s2
                                                        then putEqs $ zip args1 args2
                                                        else headSymbolMismatch s t
