{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Eval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Expression Evaluation
--
-- The example illustrates how to use compositional data types to implement
-- a small expression language, with a sub language of values, and an evaluation
-- function mapping expressions to values.
--
--------------------------------------------------------------------------------

module Examples.Eval where

import Data.Comp
import Data.Comp.Show ()
import Data.Comp.Derive

-- Signature for values and operators
data Value e = Const Int | Pair e e
data Op e = Add e e | Mult e e | Fst e | Snd e

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [makeFunctor, makeShowF,
          makeEqF, smartConstructors] [''Value, ''Op])

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

$(derive [liftSum] [''Eval])

-- Lift the evaluation algebra to a catamorphism
eval :: (Functor f, Eval f v) => Term f -> Term v
eval = cata evalAlg

instance (Value :<: v) => Eval Value v where
  evalAlg = inject

instance (Value :<: v) => Eval Op v where
  evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
  evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
  evalAlg (Fst x)    = fst $ projP x
  evalAlg (Snd x)    = snd $ projP x

projC :: (Value :<: v) => Term v -> Int
projC v = case project v of Just (Const n) -> n

projP :: (Value :<: v) => Term v -> (Term v, Term v)
projP v = case project v of Just (Pair x y) -> (x,y)

-- Example: evalEx = iConst 5
evalEx :: Term Value
evalEx = eval ((iConst 1) `iAdd` (iConst 2 `iMult` iConst 2) :: Term Sig)