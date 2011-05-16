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
-- Expression Evaluation
--
-- The example illustrates how to use parametric compositional data types to
-- implement a small expression language, with a language of values, and
-- an evaluation function mapping expressions to values. The example
-- demonstrates how (parametric) abstractions are mapped to general functions,
-- from values to values, and how it is possible to project a general value
-- (with functions) back into ground values, that can again be analysed.
--
--------------------------------------------------------------------------------

module Examples.Param.Eval where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Show ()
import Data.Comp.Param.Derive

-- Signatures for values and operators
data Const a e = Const Int
data Lam a e = Lam (a -> e) -- Note: not e -> e
data App a e = App e e
data Op a e = Add e e | Mult e e
data Fun a e = Fun (e -> e) -- Note: not a -> e

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op
-- Signature for values. Note the use of 'Fun' rather than 'Lam' (!)
type Value = Const :+: Fun
-- Signature for ground values.
type GValue = Const

-- Derive boilerplate code using Template Haskell
$(derive [instanceDifunctor, instanceEqD, instanceShowD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op])
$(derive [instanceDitraversable]
         [''Const, ''App, ''Op])
$(derive [smartConstructors] [''Fun])

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

$(derive [liftSum] [''Eval])

-- Lift the evaluation algebra to a catamorphism
eval :: (Difunctor f, Eval f v) => Term f -> Term v
eval = cata evalAlg

instance (Const :<: v) => Eval Const v where
  evalAlg (Const n) = iConst n

instance (Const :<: v) => Eval Op v where
  evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
  evalAlg (Mult x y) = iConst $ (projC x) * (projC y)

instance (Fun :<: v) => Eval App v where
  evalAlg (App x y) = (projF x) y

instance (Fun :<: v) => Eval Lam v where
  evalAlg (Lam f) = iFun f

projC :: (Const :<: v) => Term v -> Int
projC v = case project v of Just (Const n) -> n

projF :: (Fun :<: v) => Term v -> Term v -> Term v
projF v = case project v of Just (Fun f) -> f

-- |Evaluation of expressions to ground values.
evalG :: Term Sig -> Maybe (Term GValue)
evalG = deepProject . (eval :: Term Sig -> Term Value)

-- Example: evalEx = Just (iConst 4)
evalEx :: Maybe (Term GValue)
evalEx = evalG $ (iLam $ \x -> Place x `iAdd` Place x) `iApp` iConst 2