{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module Functions.ALaCarte.FreeVars where

import DataTypes.ALaCarte
import Data.ALaCarte.Variables
import Data.ALaCarte.Sum
import Data.ALaCarte
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Foldable as F

-- we interpret integers as variables here


instance HasVars Value Int where
    isVar (VInt i) = Just i
    isVar _ = Nothing

instance HasVars Op Int where

instance HasVars Sugar Int where

contVar :: Int -> SugarExpr -> Bool
contVar = containsVar


freeVars :: SugarExpr -> Set Int
freeVars = variables

contVar' :: Int -> SugarExpr -> Bool
contVar' i = cata alg
    where alg :: SugarSig Bool -> Bool
          alg x = case proj x of
                    Just (VInt j) -> i == j
                    _ -> F.foldl (||) False x

freeVars' :: SugarExpr -> Set Int
freeVars' = cata alg
    where alg :: SugarSig (Set Int) -> (Set Int)
          alg x = case proj x of
                    Just (VInt j) -> Set.singleton j
                    _ -> F.foldl Set.union Set.empty x