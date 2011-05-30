{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs,
  KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.EvalI
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Intrinsic Expression Evaluation
--
-- The example illustrates how to use generalised parametric compositional data
-- types to implement a small expression language, and an evaluation function
-- mapping typed expressions to values.
--
--------------------------------------------------------------------------------

module Examples.MultiParam.EvalI where

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

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op

-- Derive boilerplate code using Template Haskell
$(derive [makeHDifunctor, makeEqHD, makeShowHD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op])
$(derive [makeHFoldable, makeHTraversable]
         [''Const, ''App, ''Op])

-- Term evaluation algebra
class Eval f where
  evalAlg :: Alg f I
  evalAlg = I . evalAlg'
  evalAlg' :: f I I i -> i
  evalAlg' = unI . evalAlg

$(derive [liftSum] [''Eval])

-- Lift the evaluation algebra to a catamorphism
eval :: (HDifunctor f, Eval f) => Term f i -> i
eval = unI . cata evalAlg

instance Eval Const where
  evalAlg' (Const n) = n

instance Eval Op where
  evalAlg' (Add (I x) (I y))  = x + y
  evalAlg' (Mult (I x) (I y)) = x * y

instance Eval App where
  evalAlg' (App (I f) (I x)) = f x

instance Eval Lam where
  evalAlg' (Lam f) = unI . f . I

-- Example: evalEx = 4
evalEx :: Int
evalEx = eval $ ((iLam $ \x -> Place x `iAdd` Place x) `iApp` iConst 2
                 :: Term Sig Int)