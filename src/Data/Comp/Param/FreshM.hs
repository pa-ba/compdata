{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.FreshM
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines a monad for generating fresh, abstract variables, useful
-- e.g. for defining equality on terms.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.FreshM
    (
     FreshM,
     Var,
     genVar,
     evalFreshM
    ) where

import Control.Monad.State

-- |Monad for generating fresh (abstract) variables.
newtype FreshM a = FreshM (State [String] a)
    deriving Monad

-- |Abstract notion of a variable (the constructor is hidden).
data Var = Var String
           deriving Eq

instance Show Var where
    show (Var x) = x

instance Ord Var where
    compare (Var x) (Var y) = compare x y

-- |Generate a fresh variable.
genVar :: FreshM Var
genVar = FreshM $ do xs <- get
                     case xs of
                       (x : xs') -> do {put xs'; return $ Var x}
                       _ -> fail "Unexpected empty list"

-- |Evaluate a computation that uses fresh variables.
evalFreshM :: FreshM a -> a
evalFreshM (FreshM m) = evalState m vars
    where baseVars = ['a'..'z']
          vars = map (:[]) baseVars ++ vars' 1
          vars' n = map (: show n) baseVars ++ vars' (n + 1)