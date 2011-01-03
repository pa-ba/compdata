{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module Functions.Desugar where

import DataTypes
import Data.ALaCarte

-- de-sugar

class (Functor e, Functor f) => Desugar f e where
    desugarAlg :: TermAlg f e
    desugarAlg = desugarAlg' . fmap Hole
    desugarAlg' :: Alg f (Context e a)
    desugarAlg' x = applyCxt $ desugarAlg x

desugar :: Desugar f e => Term f -> Term e
desugar = termHom desugarAlg

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