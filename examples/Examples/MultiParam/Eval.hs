{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs,
  KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.Eval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Expression Evaluation
--
-- The example illustrates how to use generalised parametric compositional data
-- types to implement a small expression language, with a language of values,
-- and an evaluation function mapping typed expressions to typed values. The
-- example demonstrates how (parametric) abstractions are mapped to general
-- functions, from values to values, and how it is possible to project a general
-- value (with functions) back into ground values, that can again be analysed.
--
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, @UndecidableInstances@, @GADTs@,
-- and @KindSignatures@.
--
--------------------------------------------------------------------------------

module Examples.MultiParam.Eval where

import Data.Comp.MultiParam hiding (Const)
import Data.Comp.MultiParam.Show ()
import Data.Comp.MultiParam.Derive

-- Signatures for values and operators
data Const :: (* -> *) -> (* -> *) -> * -> * where
    Const :: Int -> Const a e Int
data Lam :: (* -> *) -> (* -> *) -> * -> * where
    Lam :: (a i -> e j) -> Lam a e (i -> j)
data App :: (* -> *) -> (* -> *) -> * -> * where
    App :: e (i -> j) -> e i -> App a e j
data Op :: (* -> *) -> (* -> *) -> * -> * where
    Add :: e Int -> e Int -> Op a e Int
    Mult :: e Int -> e Int -> Op a e Int
data Fun :: (* -> *) -> (* -> *) -> * -> * where
    Fun :: (e i -> e j) -> Fun a e (i -> j)

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op
-- Signature for values. Note the use of 'Fun' rather than 'Lam' (!)
type Value = Const :+: Fun
-- Signature for ground values.
type GValue = Const

-- Derive boilerplate code using Template Haskell
$(derive [instanceHDifunctor, instanceEqHD, instanceShowHD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op])
$(derive [instanceHFoldable, instanceHTraversable]
         [''Const, ''App, ''Op])
$(derive [smartConstructors] [''Fun])

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

$(derive [liftSum] [''Eval])

-- Lift the evaluation algebra to a catamorphism
eval :: (HDifunctor f, Eval f v) => Term f :-> Term v
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

projC :: (Const :<: v) => Term v Int -> Int
projC v = case project v of Just (Const n) -> n

projF :: (Fun :<: v) => Term v (i -> j) -> Term v i -> Term v j
projF v = case project v of Just (Fun f) -> f

-- |Evaluation of expressions to ground values.
evalG :: Term Sig i -> Maybe (Term GValue i)
evalG = deepProject . (eval :: Term Sig :-> Term Value)

-- Example: evalEx = Just (iConst 4)
evalEx :: Maybe (Term GValue Int)
evalEx = evalG $ (iLam $ \x -> Place x `iAdd` Place x) `iApp` iConst 2