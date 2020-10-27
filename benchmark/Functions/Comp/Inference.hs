{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances,
  ConstraintKinds,
  CPP #-}

module Functions.Comp.Inference where

import Functions.Comp.Desugar
import DataTypes.Comp
import Data.Comp
import Data.Comp.Derive

-- Control.Monad.Fail import is redundant since GHC 8.8.1
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif

-- type inference

class Monad m => InferType f t m where
    inferTypeAlg :: f (Term t) -> m (Term t)

inferType :: (Traversable f, InferType f t m) => Term f -> m (Term t)
inferType = cataM inferTypeAlg

inferBaseType :: (Traversable f, InferType f ValueT m) => Term f -> m BaseType
inferBaseType = inferType

$(derive [liftSum] [''InferType])

instance (ValueT :<: t, MonadFail m) => InferType Value t m where
    inferTypeAlg (VInt _) = return $ inject TInt
    inferTypeAlg (VBool _) = return $ inject TBool
    inferTypeAlg (VPair x y) = return $ inject $ TPair x y

checkOp :: (g :<: f, Eq (g (Term f)), MonadFail m) =>
           [g (Term f)] -> g (Term f) -> [Term f] -> m (Term f)
checkOp exs et tys = if and (zipWith (\ f t -> maybe False (==f) (project t)) exs tys) 
                     then return (inject et)
                     else fail""


instance (ValueT :<: t, EqF t, MonadFail m) => InferType Op t m where
    inferTypeAlg (Plus x y) = checkOp [TInt,TInt] TInt [x ,y]
    inferTypeAlg (Mult x y) = checkOp [TInt,TInt] TInt [x ,y]
    inferTypeAlg (Lt x y) = checkOp [TInt,TInt] TBool [x ,y]
    inferTypeAlg (And x y) = checkOp [TBool,TBool] TBool [x ,y]
    inferTypeAlg (Not x) = checkOp [TBool] TBool [x]
    inferTypeAlg (If b x y) = case project b of
                                 Just TBool | x == y -> return x
                                 _ -> fail "" 
    inferTypeAlg (Eq x y) = if x == y then return iTBool else fail ""
    inferTypeAlg (Proj p x) = case project x of
                                Just (TPair x1 x2) -> 
                                    case p of
                                      ProjLeft -> return x1
                                      ProjRight -> return x2
                                _ -> fail ""

instance (ValueT :<: t, EqF t, MonadFail m) => InferType Sugar t m where
    inferTypeAlg (Minus x y) = checkOp [TInt,TInt] TInt [x ,y]
    inferTypeAlg (Neg x) = checkOp [TInt] TInt [x]
    inferTypeAlg (Gt x y) = checkOp [TInt,TInt] TBool [x ,y]
    inferTypeAlg (Or x y) = checkOp [TBool,TBool] TBool [x ,y]
    inferTypeAlg (Impl x y) = checkOp [TBool,TBool] TBool [x ,y]

desugType :: SugarExpr -> Err BaseType
desugType = inferType . (desug :: SugarExpr -> Expr)

typeSugar :: SugarExpr -> Err BaseType
typeSugar = inferType

desugTypeAlg  :: AlgM Err SugarSig BaseType
desugTypeAlg = inferTypeAlg  `compAlgM'` (desugAlg :: Hom SugarSig ExprSig)

desugType' :: SugarExpr -> Err BaseType
desugType' e = cataM desugTypeAlg e

-- pure type inference

class InferType2 f t where
    inferTypeAlg2 :: f (Term t) -> (Term t)

inferType2 :: (Functor f, InferType2 f t) => Term f -> (Term t)
inferType2 = cata inferTypeAlg2

inferBaseType2 :: (Functor f, InferType2 f ValueT) => Term f -> BaseType
inferBaseType2 = inferType2

$(derive [liftSum] [''InferType2])

instance (ValueT :<: t) => InferType2 Value t where
    inferTypeAlg2 (VInt _) = inject TInt
    inferTypeAlg2 (VBool _) = inject TBool
    inferTypeAlg2 (VPair x y) = inject $ TPair x y

checkOp2 :: (g :<: f, Eq (g (Term f))) =>
           [g (Term f)] -> g (Term f) -> [Term f] -> (Term f)
checkOp2 exs ret tys = if and (zipWith (\ f t -> maybe False (==f) (project t)) exs tys)
                       then inject ret
                       else error ""


instance (ValueT :<: t, EqF t) => InferType2 Op t where
    inferTypeAlg2 (Plus x y) = checkOp2 [TInt,TInt] TInt [x ,y]
    inferTypeAlg2 (Mult x y) = checkOp2 [TInt,TInt] TInt [x ,y]
    inferTypeAlg2 (Lt x y) = checkOp2 [TInt,TInt] TBool [x ,y]
    inferTypeAlg2 (And x y) = checkOp2 [TBool,TBool] TBool [x ,y]
    inferTypeAlg2 (Not x) = checkOp2 [TBool] TBool [x]
    inferTypeAlg2 (If b x y) = case project b of
                                 Just TBool | x == y -> x
                                 _ -> error ""
    inferTypeAlg2 (Eq x y) = if x == y then iTBool else error ""
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

desugType2 :: SugarExpr -> BaseType
desugType2 = inferType2 . (desug :: SugarExpr -> Expr)

typeSugar2 :: SugarExpr -> BaseType
typeSugar2 = inferType2

desugTypeAlg2  :: Alg SugarSig BaseType
desugTypeAlg2 = inferTypeAlg2  `compAlg` (desugAlg :: Hom SugarSig ExprSig)

desugType2' :: SugarExpr -> BaseType
desugType2' e = cata desugTypeAlg2 e
