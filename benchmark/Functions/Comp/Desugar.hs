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
import Data.Comp.Derive

-- de-sugar

class (Functor e, Traversable f) => Desug f e where
    desugAlg :: TermHom f e

desugExpr :: SugarExpr -> Expr
desugExpr = desug

desugExpr' :: SugarExpr -> Expr
desugExpr' = desug'

desug :: Desug f e => Term f -> Term e
{-# INLINE desug #-}
desug = appTermHom desugAlg

desug' :: Desug f e => Term f -> Term e
{-# INLINE desug' #-}
desug' = appTermHom' desugAlg

$(derive [liftSum] [''Desug])

instance (Value :<: v, Functor v) => Desug Value v where
    desugAlg = liftCxt

instance (Op :<: v, Functor v) => Desug Op v where
    desugAlg = liftCxt

instance (Op :<: v, Value :<: v, Functor v) => Desug Sugar v where
    desugAlg (Neg x) =  iVInt (-1) `iMult` (Hole x)
    desugAlg (Minus x y) =  (Hole x) `iPlus` ((iVInt (-1)) `iMult` (Hole y))
    desugAlg (Gt x y) =  (Hole y) `iLt` (Hole x)
    desugAlg (Or x y) = iNot (iNot (Hole x) `iAnd` iNot (Hole y))
    desugAlg (Impl x y) = iNot ((Hole x) `iAnd` iNot (Hole y))


-- standard algebraic approach

class Desug2 f g where
    desugAlg2 :: Alg f (Term g)

desugExpr2 :: SugarExpr -> Expr
desugExpr2 = desug2

desug2 :: (Functor f, Desug2 f g) => Term f -> Term g
desug2 = cata desugAlg2

$(derive [liftSum] [''Desug2])

instance (Value :<: v) => Desug2 Value v where
    desugAlg2 = inject

instance (Op :<: v) => Desug2 Op v where
    desugAlg2 = inject

instance (Op :<: v, Value :<: v, Functor v) => Desug2 Sugar v where
    desugAlg2 (Neg x) =  iVInt (-1) `iMult` x
    desugAlg2 (Minus x y) =  x `iPlus` ((iVInt (-1)) `iMult` y)
    desugAlg2 (Gt x y) =  y `iLt` x
    desugAlg2 (Or x y) = iNot (iNot x `iAnd` iNot y)
    desugAlg2 (Impl x y) = iNot (x `iAnd` iNot y)

