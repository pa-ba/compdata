{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Multi.Eval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Generalized Compositional Data Types Example: Expression Evaluation.
--
-- The example illustrates how to use generalised compositional data types 
-- to implement a small expression language, with a sub language of values, and 
-- an evaluation function mapping expressions to values.
--
--------------------------------------------------------------------------------

module Examples.Multi.Eval where

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Derive

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
$(derive [instanceHFunctor, instanceHShowF, smartHConstructors] 
         [''Value, ''Op])

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

instance (Eval f v, Eval g v) => Eval (f :+: g) v where
  evalAlg (Inl x) = evalAlg x
  evalAlg (Inr x) = evalAlg x

-- Lift the evaluation algebra to a catamorphism
eval :: (HFunctor f, Eval f v) => Term f :-> Term v
eval = cata evalAlg

instance (Value :<: v) => Eval Value v where
  evalAlg = inject

instance (Value :<: v) => Eval Op v where
  evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
  evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
  evalAlg (Fst x)    = fst $ projP x
  evalAlg (Snd x)    = snd $ projP x

projC :: (Value :<: v) => Term v Int -> Int
projC v = case project v of Just (Const n) -> n

projP :: (Value :<: v) => Term v (s,t) -> (Term v s, Term v t)
projP v = case project v of Just (Pair x y) -> (x,y)

-- Example: evalEx = iConst 2
evalEx :: Term Value Int
evalEx = eval (iFst $ iPair (iConst 2) (iConst 1) :: Term Sig Int)