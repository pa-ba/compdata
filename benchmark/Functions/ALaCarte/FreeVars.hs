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
import qualified Data.Foldable as F

-- we interpret integers as variables here


instance HasVars Value Int where
    isVar (VInt i) = Just i
    isVar _ = Nothing

instance HasVars Op Int where

instance HasVars Sugar Int where

contVar :: Int -> SugarExpr -> Bool
contVar = containsVar


freeVars :: SugarExpr -> [Int]
freeVars = variableList

contVar' :: Int -> SugarExpr -> Bool
contVar' i = cata alg
    where alg :: SugarSig Bool -> Bool
          alg x = case proj x of
                    Just (VInt j) -> i == j
                    _ -> F.foldl (||) False x

contVarGen :: Int -> SugarExpr -> Bool
contVarGen i e = elem i [ j | VInt j <- subterms' e]

freeVars' :: SugarExpr -> [Int]
freeVars' = cata alg
    where alg :: SugarSig [Int] -> [Int]
          alg x = case proj x of
                    Just (VInt j) -> [ j ]
                    _ -> F.foldl (++) [] x


freeVarsGen :: SugarExpr -> [Int]
freeVarsGen e =  [ j | VInt j <- subterms' e]