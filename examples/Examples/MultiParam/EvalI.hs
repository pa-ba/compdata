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
-- Expression Evaluation
--
-- The example illustrates how to use parametric compositional data types to
-- implement a small expression language, with a language of values, and
-- an evaluation function mapping expressions to values. The example
-- demonstrates how (parametric) abstractions are mapped to general functions,
-- from values to values, and how it is possible to project a general value
-- (with functions) back into ground values, that can again be analysed.
--
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.
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
    Lam :: (a :~> e) (i -> j) -> Lam a e (i -> j)
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
class Eval f where
  evalAlg :: Alg f I

$(derive [liftSum] [''Eval])

-- Lift the evaluation algebra to a catamorphism
eval :: (HDifunctor f, Eval f) => Term f i -> i
eval = unI . cata evalAlg

instance Eval Const where
  evalAlg (Const n) = I n

instance Eval Op where
  evalAlg (Add (I x) (I y))  = I (x + y)
  evalAlg (Mult (I x) (I y)) = I (x * y)

instance Eval App where
  evalAlg (App (I x) (I y)) = I (x y)

instance Eval Lam where
  evalAlg (Lam ((:~>) f)) = I (unI . f . I)

-- Example: evalEx = 4
evalEx :: Int
evalEx = eval $ ((iLam . (:~>) $ \x -> Place x `iAdd` Place x) `iApp` iConst 2 :: Term Sig Int)