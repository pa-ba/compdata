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


-- standard algebraic approach

class Desugar2 f g where
    desugarAlg2 :: Alg f (Term g)

desugarExpr2 :: SugarExpr -> Expr
desugarExpr2 = desugar2

desugar2 :: (Functor f, Desugar2 f g) => Term f -> Term g
desugar2 = cata desugarAlg2

instance (Desugar2 f e, Desugar2 g e) => Desugar2 (f :+: g) e where
    desugarAlg2 (Inl v) = desugarAlg2 v
    desugarAlg2 (Inr v) = desugarAlg2 v

instance (Value :<: v) => Desugar2 Value v where
    desugarAlg2 = inject

instance (Op :<: v) => Desugar2 Op v where
    desugarAlg2 = inject

instance (Op :<: v, Value :<: v, Functor v) => Desugar2 Sugar v where
    desugarAlg2 (Neg x) =  iVInt (-1) `iMult` x
    desugarAlg2 (Minus x y) =  x `iPlus` ((iVInt (-1)) `iMult` y)
    desugarAlg2 (Gt x y) =  y `iLt` x
    desugarAlg2 (Or x y) = iNot (iNot x `iAnd` iNot y)
    desugarAlg2 (Impl x y) = iNot (x `iAnd` iNot y)

