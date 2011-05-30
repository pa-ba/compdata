{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Multi.EvalI
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Intrinsic Expression Evaluation
--
-- The example illustrates how to use generalised compositional data types 
-- to implement a small expression language, and  an evaluation function mapping
-- intrinsically typed expressions to values.
--
--------------------------------------------------------------------------------

module Examples.Multi.EvalI where

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Derive

-- Signature for values and operators
data Value e l where
  Const  ::        Int -> Value e Int
  Pair   :: e s -> e t -> Value e (s,t)
data Op e l where
  Add, Mult  :: e Int -> e Int   -> Op e Int
  Fst        ::          e (s,t) -> Op e s
  Snd        ::          e (s,t) -> Op e t

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell (GHC 7 needed)
$(derive [makeHFunctor, makeHShowF, makeHEqF, smartConstructors] 
         [''Value, ''Op])

-- Term evaluation algebra
class EvalI f where
  evalAlgI :: Alg f I

$(derive [liftSum] [''EvalI])

-- Lift the evaluation algebra to a catamorphism
evalI :: (HFunctor f, EvalI f) => Term f i -> i
evalI = unI . cata evalAlgI

instance EvalI Value where
  evalAlgI (Const n) = I n
  evalAlgI (Pair (I x) (I y)) = I (x,y)

instance EvalI Op where
  evalAlgI (Add (I x) (I y))  = I (x + y)
  evalAlgI (Mult (I x) (I y)) = I (x * y)
  evalAlgI (Fst (I (x,_)))    = I x
  evalAlgI (Snd (I (_,y)))    = I y

-- Example: evalEx = 2
evalIEx :: Int
evalIEx = evalI (iFst $ iPair (iConst 2) (iConst 1) :: Term Sig Int)