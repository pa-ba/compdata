{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Eval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Parametric Compositional Data Types Example: Expression Evaluation.
--
-- The example illustrates how to use parametric compositional data types to
-- implement a small expression language, with a language of values, and
-- an evaluation function mapping expressions to values.
--
--------------------------------------------------------------------------------

module Examples.Param.Eval where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Derive

-- Signature for values and operators
data Const a e = Const Int
data Lam a e = Lam (a -> e)
data App a e = App e e
data Add a e = Add e e
data Fun a e = Fun (e -> e)

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Add
-- Signature for values. Note the use of 'Fun' rather than 'Lam' (!)
type Value = Const :+: Fun

-- Derive boilerplate code using Template Haskell
$(derive [instanceDifunctor, smartConstructors] [''Const, ''Lam, ''App, ''Add])
$(derive [smartConstructors] [''Fun])

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

instance (Eval f v, Eval g v) => Eval (f :+: g) v where
  evalAlg (Inl x) = evalAlg x
  evalAlg (Inr x) = evalAlg x

-- Lift the evaluation algebra to a catamorphism
eval :: (Difunctor f, Eval f v) => Term f -> Term v
eval = cata evalAlg

instance (Const :<: v) => Eval Const v where
  evalAlg (Const n) = iConst n

instance (Const :<: v) => Eval Add v where
  evalAlg (Add x y) = iConst $ (projC x) + (projC y)

instance (Fun :<: v) => Eval App v where
  evalAlg (App x y)  = (projF x) y

instance (Fun :<: v) => Eval Lam v where
  evalAlg (Lam f)  = iFun f

projC :: (Const :<: v) => Term v -> Int
projC v = case project v of Just (Const n) -> n

projF :: (Fun :<: v) => Term v -> Term v -> Term v
projF v = case project v of Just (Fun f) -> f

-- Example: evalEx = iConst 4
evalEx :: Term Value
evalEx = eval ((iLam $ \x -> Hole x `iAdd` Hole x) `iApp` iConst 2 :: Term Sig)