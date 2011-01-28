{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module Functions.Comp.Inference where

import Functions.Comp.Desugar
import DataTypes.Comp
import Data.Comp
import Data.Traversable

-- type inference

class Monad m => InferType f t m where
    inferTypeAlg :: f (Term t) -> m (Term t)

inferType :: (Traversable f, InferType f t m) => Term f -> m (Term t)
inferType = cataM inferTypeAlg

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

instance (ValueT :<: t, EqF t, Monad m) => InferType Sugar t m where
    inferTypeAlg (Minus x y) = checkOp [TInt,TInt] TInt [x ,y]
    inferTypeAlg (Neg x) = checkOp [TInt] TInt [x]
    inferTypeAlg (Gt x y) = checkOp [TInt,TInt] TBool [x ,y]
    inferTypeAlg (Or x y) = checkOp [TBool,TBool] TBool [x ,y]
    inferTypeAlg (Impl x y) = checkOp [TBool,TBool] TBool [x ,y]

desugarType :: SugarExpr -> Err BaseType
desugarType = inferType . (desugar :: SugarExpr -> Expr)

typeSugar :: SugarExpr -> Err BaseType
typeSugar = inferType

desugarTypeAlg  :: AlgM Err SugarSig BaseType
desugarTypeAlg = inferTypeAlg  `compAlgM'` (desugarAlg :: TermHom SugarSig ExprSig)

desugarType' :: SugarExpr -> Err BaseType
desugarType' e = cataM desugarTypeAlg e

-- pure type inference

class InferType2 f t where
    inferTypeAlg2 :: f (Term t) -> (Term t)

inferType2 :: (Functor f, InferType2 f t) => Term f -> (Term t)
inferType2 = cata inferTypeAlg2

inferBaseType2 :: (Functor f, InferType2 f ValueT) => Term f -> BaseType
inferBaseType2 = inferType2

instance (InferType2 f t, InferType2 g t) => InferType2 (f :+: g) t where
    inferTypeAlg2 (Inl v) = inferTypeAlg2 v
    inferTypeAlg2 (Inr v) = inferTypeAlg2 v

instance (ValueT :<: t) => InferType2 Value t where
    inferTypeAlg2 (VInt _) = inject TInt
    inferTypeAlg2 (VBool _) = inject TBool
    inferTypeAlg2 (VPair x y) = inject $ TPair x y

check2:: (g :<: f, Eq (g (Term f))) =>
        g (Term f) -> Term f -> a -> a
check2 f t z = if project t == Just f then z else error ""

checkEq2 :: (Eq a) => a -> a -> b -> b
checkEq2 x y z = if x == y then z else error ""

runCheck :: [a -> a] -> a -> a
runCheck = foldr (.) id

checkOp2 :: (g :<: f, Eq (g (Term f))) =>
           [g (Term f)] -> g (Term f) -> [Term f] -> (Term f)
checkOp2 exs ret tys = runCheck (zipWith check2 exs tys) (inject ret)


instance (ValueT :<: t, EqF t) => InferType2 Op t where
    inferTypeAlg2 (Plus x y) = checkOp2 [TInt,TInt] TInt [x ,y]
    inferTypeAlg2 (Mult x y) = checkOp2 [TInt,TInt] TInt [x ,y]
    inferTypeAlg2 (Lt x y) = checkOp2 [TInt,TInt] TBool [x ,y]
    inferTypeAlg2 (And x y) = checkOp2 [TBool,TBool] TBool [x ,y]
    inferTypeAlg2 (Not x) = checkOp2 [TBool] TBool [x]
    inferTypeAlg2 (If b x y) = checkEq2 x y $ check2 TBool b $ x
    inferTypeAlg2 (Eq x y) = checkEq2 x y $ iTBool
    inferTypeAlg2 (Proj p x) = case project x of
                                Just (TPair x1 x2) -> 
                                    case p of
                                      ProjLeft -> x1
                                      ProjRight -> x2
                                _ -> error ""

instance (ValueT :<: t, EqF t) => InferType2 Sugar t where
    inferTypeAlg2 (Minus x y) = checkOp2 [TInt,TInt] TInt [x ,y]
    inferTypeAlg2 (Neg x) = checkOp2 [TInt] TInt [x]
    inferTypeAlg2 (Gt x y) = checkOp2 [TInt,TInt] TBool [x ,y]
    inferTypeAlg2 (Or x y) = checkOp2 [TBool,TBool] TBool [x ,y]
    inferTypeAlg2 (Impl x y) = checkOp2 [TBool,TBool] TBool [x ,y]

desugarType2 :: SugarExpr -> BaseType
desugarType2 = inferType2 . (desugar :: SugarExpr -> Expr)

typeSugar2 :: SugarExpr -> BaseType
typeSugar2 = inferType2

desugarTypeAlg2  :: Alg SugarSig BaseType
desugarTypeAlg2 = inferTypeAlg2  `compAlg` (desugarAlg :: TermHom SugarSig ExprSig)

desugarType2' :: SugarExpr -> Err BaseType
desugarType2' e = cataM desugarTypeAlg e