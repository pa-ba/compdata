{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module Functions.Inference where

import Functions.Desugar
import DataTypes
import Data.ALaCarte
import Data.Traversable

-- type inference

class Monad m => InferType f t m where
    inferTypeAlg :: f (Term t) -> m (Term t)

inferType :: (Traversable f, InferType f t m) => Term f -> m (Term t)
inferType = algHomM inferTypeAlg

inferBaseType :: (Traversable f, InferType f ValueT m) => Term f -> m BaseType
inferBaseType = inferType

instance (InferType f t m, InferType g t m) => InferType (f :+: g) t m where
    inferTypeAlg (Inl v) = inferTypeAlg v
    inferTypeAlg (Inr v) = inferTypeAlg v

instance (ValueT :<: t, Monad m) => InferType Value t m where
    inferTypeAlg (VInt _) = return $ inject TInt
    inferTypeAlg (VBool _) = return $ inject TBool
    inferTypeAlg (VPair x y) = return $ inject $ TPair x y

check:: (g :<: f, Eq (g (Term f)), Monad m) =>
        g (Term f) -> Term f -> m ()
check f t = if project t == Just f then return () else fail ""

checkEq :: (Eq a, Monad m) => a -> a -> m ()
checkEq x y = if x == y then return () else fail ""

checkOp :: (g :<: f, Eq (g (Term f)), Monad m) =>
           [g (Term f)] -> g (Term f) -> [Term f] -> m (Term f)
checkOp exs ret tys = sequence_ (zipWith check exs tys) >> return $ inject ret


instance (ValueT :<: t, EqF t, Monad m) => InferType Op t m where
    inferTypeAlg (Plus x y) = checkOp [TInt,TInt] TInt [x ,y]
    inferTypeAlg (Mult x y) = checkOp [TInt,TInt] TInt [x ,y]
    inferTypeAlg (Lt x y) = checkOp [TInt,TInt] TBool [x ,y]
    inferTypeAlg (And x y) = checkOp [TBool,TBool] TBool [x ,y]
    inferTypeAlg (Not x) = checkOp [TBool] TBool [x]
    inferTypeAlg (If b x y) = check TBool b >> checkEq x y >> return x
    inferTypeAlg (Eq x y) = checkEq x y >> return $ iTBool
    inferTypeAlg (Proj p x) = case project x of
                                Just (TPair x1 x2) -> return $
                                    case p of
                                      ProjLeft -> x1
                                      ProjRight -> x2
                                _ -> fail ""


desugarType :: SugarExpr -> Err BaseType
desugarType = inferType . (desugar :: SugarExpr -> Expr)

desugarTypeAlg  :: AlgM Err SugarSig BaseType
desugarTypeAlg = inferTypeAlg  `compAlgM'` (desugarAlg :: TermAlg SugarSig ExprSig)

desugarType' :: SugarExpr -> Err BaseType
desugarType' e = algHomM desugarTypeAlg e