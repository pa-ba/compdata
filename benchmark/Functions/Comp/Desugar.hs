{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module Functions.Comp.Desugar where

import DataTypes.Comp
import Data.Comp

-- de-sugar

class (Functor e, Functor f) => Desugar f e where
    desugarAlg :: TermHom f e
    desugarAlg = desugarAlg' . fmap Hole
    desugarAlg' :: Alg f (Context e a)
    desugarAlg' x = applyCxt $ desugarAlg x

desugarExpr :: SugarExpr -> Expr
desugarExpr = desugar

desugar :: Desugar f e => Term f -> Term e
desugar = applyTermHom desugarAlg

instance (Desugar f e, Desugar g e) => Desugar (g :+: f) e where
    desugarAlg (Inl v) = desugarAlg v
    desugarAlg (Inr v) = desugarAlg v

instance (Value :<: v, Functor v) => Desugar Value v where
    desugarAlg = liftCxt

instance (Op :<: v, Functor v) => Desugar Op v where
    desugarAlg = liftCxt

instance (Op :<: v, Value :<: v, Functor v) => Desugar Sugar v where
    desugarAlg' (Neg x) =  iVInt (-1) `iMult` x
    desugarAlg' (Minus x y) =  x `iPlus` ((iVInt (-1)) `iMult` y)
    desugarAlg' (Gt x y) =  y `iLt` x
    desugarAlg' (Or x y) = iNot (iNot x `iAnd` iNot y)
    desugarAlg' (Impl x y) = iNot (x `iAnd` iNot y)