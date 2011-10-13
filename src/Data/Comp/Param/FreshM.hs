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
     getVar,
     nextVar,
     evalFreshM
    ) where

import Control.Monad.Reader

-- |Monad for generating fresh (abstract) variables.
newtype FreshM a = FreshM{unFreshM :: Reader [String] a}
    deriving Monad

-- |Abstract notion of a variable (the constructor is hidden).
data Var = Var String
           deriving Eq

instance Show Var where
    show (Var x) = x

instance Ord Var where
    compare (Var x) (Var y) = compare x y

-- |Get the current variable.
getVar :: FreshM Var
getVar = FreshM $ asks (Var . head)

-- |Use the next available variable in the monadic computation.
nextVar :: FreshM a -> FreshM a
nextVar = FreshM . local tail . unFreshM

-- |Evaluate a computation that uses fresh variables.
evalFreshM :: FreshM a -> a
evalFreshM (FreshM m) = runReader m vars
    where baseVars = ['a'..'z']
          vars = map (:[]) baseVars ++ vars' 1
          vars' n = map (: show n) baseVars ++ vars' (n + 1)