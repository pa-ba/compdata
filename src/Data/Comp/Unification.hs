{-# LANGUAGE FlexibleContexts #-}

-------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Unification
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module implements a simple unification algorithm using data
-- types a la carte.
--
--------------------------------------------------------------------------------
module Data.Comp.Unification where

import Data.Comp.Term
import Data.Comp.Variables
import Data.Comp.Decompose

import Control.Monad.Error
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

instance Error (UnifError f v) where
    strMsg = UnifError


failedOccursCheck :: (MonadError (UnifError f v) m) => v -> Term f -> m a
failedOccursCheck v t = throwError $ FailedOccursCheck v t

headSymbolMismatch :: (MonadError (UnifError f v) m) => Term f -> Term f -> m a
headSymbolMismatch f g = throwError $ HeadSymbolMismatch f g

appSubstEq :: (Ord v,  HasVars f v, Functor f) =>
     Subst f v -> Equation f -> Equation f
appSubstEq s (t1,t2) = (appSubst s t1,appSubst s t2)


{-| This function returns the most general unifier of the given
equations using the algorithm of Martelli and Montanari. -}

unify :: (MonadError (UnifError f v) m, Decompose f v, Ord v, Eq (Const f))
      => Equations f -> m (Subst f v)
unify = runUnifyM runUnify

data UnifyState f v = UnifyState {usEqs ::Equations f, usSubst :: Subst f v}
type UnifyM f v m a = StateT (UnifyState f v) m a

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

putBinding :: (Monad m, Ord v, HasVars f v, Functor f) => (v, Term f) -> UnifyM f v m ()
putBinding bind = modify appSubst
    where binds = Map.fromList [bind]
          appSubst s = s { usEqs = map (appSubstEq binds) (usEqs s),
                             usSubst = compSubst binds (usSubst s)}


runUnify :: (MonadError (UnifError f v) m, Decompose f v, Ord v, Eq (Const f))
         => UnifyM f v m ()
runUnify = withNextEq (\ e -> unifyStep e >> runUnify)

unifyStep :: (MonadError (UnifError f v) m, Decompose f v, Ord v, Eq (Const f)) 
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