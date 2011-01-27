{-# LANGUAGE
  GADTs,
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances#-}

module Multi.Functions.ALaCarte.Eval where

import Multi.DataTypes.ALaCarte
import Multi.Functions.ALaCarte.Desugar
import Data.ALaCarte.Multi
import Data.ALaCarte.Multi.HEquality

-- evaluation

class Eval e v where
    evalAlg :: Alg e (Term v)

eval :: (HFunctor e, Eval e v) => Term e :-> (Term v)
eval = cata evalAlg

instance (Eval f v, Eval g v) => Eval (f :++: g) v where
    evalAlg (HInl v) = evalAlg v
    evalAlg (HInr v) = evalAlg v

instance (Value :<<: v) => Eval Value v where
    evalAlg = inject


getInt :: (Value :<<: v) => Term v Int -> Int
getInt t = case project t of
             Just (VInt x) -> x
             Nothing -> undefined
getBool :: (Value :<<: v) => Term v Bool -> Bool
getBool t = case project t of
             Just (VBool x) -> x
             Nothing -> undefined

getPair :: (Value :<<: v) => Term v (s,t) -> ((Term v s), (Term v t))
getPair t = case project t of
              Just (VPair x y) -> (x, y)
              Nothing -> undefined


instance (Value :<<: v, HEqF v) => Eval Op v where
    evalAlg (Plus x y) = iVInt $ getInt x + getInt y
    evalAlg (Mult x y) = iVInt $ getInt x * getInt y
    evalAlg (If b x y) = if getBool b then x else y
    evalAlg (Eq x y) = iVBool $ x == y
    evalAlg (Lt x y) = iVBool $ getInt x < getInt y
    evalAlg (And x y) = iVBool $ getBool x && getBool y
    evalAlg (Not x) = iVBool $ not $ getBool x
    evalAlg (ProjLeft x) = fst $ getPair x
    evalAlg (ProjRight x) = snd $ getPair x

instance (Value :<<: v) => Eval Sugar v where
    evalAlg (Neg x) = iVInt $ negate $ getInt x
    evalAlg (Minus x y) = iVInt $ getInt x - getInt y
    evalAlg (Gt x y) = iVBool $ getInt x > getInt y
    evalAlg (Or x y) = iVBool $ getBool x || getBool y
    evalAlg (Impl x y) = iVBool $ not (getBool x) || getBool y

desugarEval :: SugarExpr :-> ValueExpr
desugarEval = eval . (desugar :: SugarExpr :-> Expr)

evalSugar :: SugarExpr :-> ValueExpr
evalSugar = eval

desugarEvalAlg  :: Alg SugarSig ValueExpr
desugarEvalAlg = evalAlg  `compAlg` (desugarAlg :: TermHom SugarSig ExprSig)

desugarEval' :: SugarExpr :-> ValueExpr
desugarEval' e = cata desugarEvalAlg e