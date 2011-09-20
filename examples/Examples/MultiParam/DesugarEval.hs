{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  TypeSynonymInstances, OverlappingInstances, GADTs, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.DesugarEval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Desugaring + Expression Evaluation
--
-- The example illustrates how to compose a term homomorphism and an algebra,
-- exemplified via a desugaring term homomorphism and an evaluation algebra.
--
-- The example extends the example from 'Examples.MultiParam.Eval'.
--
--------------------------------------------------------------------------------

module Examples.MultiParam.DesugarEval where

import Data.Comp.MultiParam hiding (Const)
import Data.Comp.MultiParam.Show ()
import Data.Comp.MultiParam.Derive
import Data.Comp.MultiParam.Desugar

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
data IfThenElse :: (* -> *) -> (* -> *) -> * -> * where
                   IfThenElse :: (e Int) -> (e i) -> (e i) -> IfThenElse a e i

-- Signature for syntactic sugar (negation, let expressions)
data Sug :: (* -> *) -> (* -> *) -> * -> * where
            Neg :: e Int -> Sug a e Int
            Let :: e i -> (a i -> e j) -> Sug a e j

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op :+: IfThenElse
-- Signature for the simple expression language with syntactic sugar
type Sig' = Sug :+: Sig
-- Signature for values. Note the use of 'Fun' rather than 'Lam' (!)
type Value = Const :+: Fun
-- Signature for ground values.
type GValue = Const

-- Derive boilerplate code using Template Haskell
$(derive [makeHDifunctor, makeEqHD, makeOrdHD, makeShowHD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op, ''IfThenElse, ''Sug])
$(derive [makeHFoldable, makeHTraversable]
         [''Const, ''App, ''Op])

instance (Op :<: f, Const :<: f, Lam :<: f, App :<: f, HDifunctor f)
  => Desugar Sug f where
  desugHom' (Neg x)   = iConst (-1) `iMult` x
  desugHom' (Let x y) = inject (Lam y) `iApp` x

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

$(derive [liftSum] [''Eval])

-- Compose the evaluation algebra and the desugaring homomorphism to an algebra
eval :: Term Sig' :-> Term Value
eval = cata (evalAlg `compAlg` (desugHom :: Hom Sig' Sig))

instance (Const :<: v) => Eval Const v where
  evalAlg (Const n) = iConst n

instance (Const :<: v) => Eval Op v where
  evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
  evalAlg (Mult x y) = iConst $ (projC x) * (projC y)

instance (Fun :<: v) => Eval App v where
  evalAlg (App x y) = (projF x) y

instance (Fun :<: v) => Eval Lam v where
  evalAlg (Lam f) = inject $ Fun f

instance (Const :<: v) => Eval IfThenElse v where
  evalAlg (IfThenElse c v1 v2) = if projC c /= 0 then v1 else v2

projC :: (Const :<: v) => Term v Int -> Int
projC v = case project v of Just (Const n) -> n

projF :: (Fun :<: v) => Term v (i -> j) -> Term v i -> Term v j
projF v = case project v of Just (Fun f) -> f

-- |Evaluation of expressions to ground values.
evalG :: Term Sig' i -> Maybe (Term GValue i)
evalG = deepProject . (eval :: Term Sig' :-> Term Value)

-- Example: evalEx = Just (iConst -6)
evalEx :: Maybe (Term GValue Int)
evalEx = evalG $ iLet (iConst 6) $ \x -> iNeg x