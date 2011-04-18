{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.FreshM
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
module Data.Comp.MultiParam.FreshM
    (
     FreshM,
     Var,
     varEq,
     varCompare,
     varShow,
     genVar,
     varCoerce,
     evalFreshM
    ) where

import Control.Monad.State

-- |Monad for generating fresh (abstract) variables.
newtype FreshM a = FreshM (State [String] a)
    deriving Monad

-- |Abstract notion of a variable (the constructor is hidden).
data Var i = Var String

-- |Equality on variables.
varEq :: Var i -> Var j -> Bool
varEq (Var x) (Var y) = x == y

-- |Ordering of variables.
varCompare :: Var i -> Var j -> Ordering
varCompare (Var x) (Var y) = compare x y

-- |Printing of variables.
varShow :: Var i -> String
varShow (Var x) = x

-- |Change the type of a variable.
varCoerce :: Var i -> Var j
varCoerce (Var x) = Var x

-- |Generate a fresh variable.
genVar :: FreshM (Var i)
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