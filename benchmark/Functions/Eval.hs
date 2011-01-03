{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module Functions.Eval where

import DataTypes
import Functions.Desugar
import Data.ALaCarte
import Control.Monad
import Data.Traversable

-- evaluation

class Monad m => Eval e v m where
    evalAlg :: e (Term v) -> m (Term v)

eval :: (Traversable e, Eval e v m) => Term e -> m (Term v)
eval = algHomM evalAlg

instance (Eval f v m, Eval g v m) => Eval (f :+: g) v m where
    evalAlg (Inl v) = evalAlg v
    evalAlg (Inr v) = evalAlg v

instance (Value :<: v, Monad m) => Eval Value v m where
    evalAlg = return . inject

coerceInt :: (Value :<: v, Monad m) => Term v -> m Int
coerceInt t = case project t of
                Just (VInt i) -> return i
                _ -> fail ""

coerceBool :: (Value :<: v, Monad m) => Term v -> m Bool
coerceBool t = case project t of
                Just (VBool b) -> return b
                _ -> fail ""

coercePair :: (Value :<: v, Monad m) => Term v -> m (Term v, Term v)
coercePair t = case project t of
                Just (VPair x y) -> return (x,y)
                _ -> fail ""

instance (Value :<: v, EqF v, Monad m) => Eval Op v m where
    evalAlg (Plus x y) = liftM2 (\ i j -> iVInt (i + j)) (coerceInt x) (coerceInt y)
    evalAlg (Mult x y) = liftM2 (\ i j -> iVInt (i * j)) (coerceInt x) (coerceInt y)
    evalAlg (If b x y) = liftM select (coerceBool b)
        where select b' = if b' then x else y
    evalAlg (Eq x y) = return $ iVBool (x == y)
    evalAlg (Lt x y) = liftM2 (\ i j -> iVBool (i < j)) (coerceInt x) (coerceInt y)
    evalAlg (And x y) = liftM2 (\ b c -> iVBool (b && c)) (coerceBool x) (coerceBool y)
    evalAlg (Not x) = liftM (iVBool . not) (coerceBool x)
    evalAlg (Proj p x) = liftM select (coercePair x)
        where select (x,y) = case p of 
                               ProjLeft -> x
                               ProjRight -> y
-- evaluation2

class Eval2 e v where
    eval2Alg :: e (Term v) -> Term v

eval2 :: (Traversable e, Eval2 e v) => Term e -> Term v
eval2 = algHom eval2Alg

instance (Eval2 f v, Eval2 g v) => Eval2 (f :+: g) v where
    eval2Alg (Inl v) = eval2Alg v
    eval2Alg (Inr v) = eval2Alg v

instance (Value :<: v) => Eval2 Value v where
    eval2Alg = inject

coerceInt2 :: (Value :<: v) => Term v -> Int
coerceInt2 t = case project t of
                Just (VInt i) -> i
                _ -> undefined

coerceBool2 :: (Value :<: v) => Term v -> Bool
coerceBool2 t = case project t of
                Just (VBool b) -> b
                _ -> undefined

coercePair2 :: (Value :<: v) => Term v -> (Term v, Term v)
coercePair2 t = case project t of
                Just (VPair x y) -> (x,y)
                _ -> undefined

instance (Value :<: v, EqF v) => Eval2 Op v where
    eval2Alg (Plus x y) = (\ i j -> iVInt (i + j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (Mult x y) = (\ i j -> iVInt (i * j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (If b x y) = select (coerceBool2 b)
        where select b' = if b' then x else y
    eval2Alg (Eq x y) = iVBool (x == y)
    eval2Alg (Lt x y) = (\ i j -> iVBool (i < j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (And x y) = (\ b c -> iVBool (b && c)) (coerceBool2 x) (coerceBool2 y)
    eval2Alg (Not x) = (iVBool . not) (coerceBool2 x)
    eval2Alg (Proj p x) = select (coercePair2 x)
        where select (x,y) = case p of 
                               ProjLeft -> x
                               ProjRight -> y

-- desugar

desugarEval :: SugarExpr -> Err ValueExpr
desugarEval = eval . (desugar :: SugarExpr -> Expr)


desugarEvalAlg  :: AlgM Err SugarSig ValueExpr
desugarEvalAlg = evalAlg  `compAlgM'` (desugarAlg :: TermAlg SugarSig ExprSig)


desugarEval' :: SugarExpr -> Err ValueExpr
desugarEval' e = algHomM desugarEvalAlg e

desugarEval2 :: SugarExpr -> ValueExpr
desugarEval2 = eval2 . (desugar :: SugarExpr -> Expr)


desugarEval2Alg  :: Alg SugarSig ValueExpr
desugarEval2Alg = eval2Alg  `compAlg` (desugarAlg :: TermAlg SugarSig ExprSig)


desugarEval2' :: SugarExpr -> ValueExpr
desugarEval2' e = algHom desugarEval2Alg e