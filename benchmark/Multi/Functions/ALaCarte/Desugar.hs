{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances,
  GADTs#-}

module Multi.Functions.ALaCarte.Desugar where

import Multi.DataTypes.ALaCarte
import Data.ALaCarte.Multi

-- de-sugar

class (HFunctor e, HFunctor f) => Desugar f e where
    desugarAlg :: TermHom f e
    desugarAlg = desugarAlg' . hfmap Hole
    desugarAlg' :: Alg f (Context e a)
    desugarAlg' x = applyCxt $ desugarAlg x

desugarExpr :: SugarExpr :-> Expr
desugarExpr = desugar

desugar :: Desugar f e => Term f :-> Term e
desugar = applyTermHom desugarAlg

instance (Desugar f e, Desugar g e) => Desugar (g :++: f) e where
    desugarAlg (HInl v) = desugarAlg v
    desugarAlg (HInr v) = desugarAlg v

instance (Value :<<: v, HFunctor v) => Desugar Value v where
    desugarAlg = liftCxt

instance (Op :<<: v, HFunctor v) => Desugar Op v where
    desugarAlg = liftCxt

instance (Op :<<: v, Value :<<: v, HFunctor v) => Desugar Sugar v where
    desugarAlg' (Neg x) =  iVInt (-1) `iMult` x
    desugarAlg' (Minus x y) =  x `iPlus` ((iVInt (-1)) `iMult` y)
    desugarAlg' (Gt x y) =  y `iLt` x
    desugarAlg' (Or x y) = iNot (iNot x `iAnd` iNot y)
    desugarAlg' (Impl x y) = iNot (x `iAnd` iNot y)