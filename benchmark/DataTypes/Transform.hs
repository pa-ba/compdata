{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module DataTypes.Transform where

import Data.Comp
import Data.Comp.ExpFunctor
import DataTypes.Standard
import DataTypes.Comp

class TransSugar f where
    transSugarAlg :: Alg f PExpr

transSugar :: (Functor f, TransSugar f) => Term f -> PExpr
transSugar = cata transSugarAlg

instance (TransSugar f, TransSugar g) => TransSugar (f :+: g) where
    transSugarAlg (Inl v) = transSugarAlg v
    transSugarAlg (Inr v) = transSugarAlg v

instance TransSugar Value where
    transSugarAlg (VInt i) = PInt i
    transSugarAlg (VBool b) = PBool b
    transSugarAlg (VPair x y) = PPair x y

instance TransSugar Op where
    transSugarAlg (Plus x y) = PPlus x y
    transSugarAlg (Mult x y) = PMult x y
    transSugarAlg (If b x y) = PIf b x y
    transSugarAlg (Lt x y) = PLt x y
    transSugarAlg (And x y) = PAnd x y
    transSugarAlg (Not x) = PNot x
    transSugarAlg (Proj p x) = PProj (ptrans p) x
        where ptrans ProjLeft = SProjLeft
              ptrans ProjRight = SProjRight
    transSugarAlg (Eq x y) = PEq x y

instance TransSugar Sugar where
    transSugarAlg (Neg x) = PNeg x
    transSugarAlg (Minus x y) = PMinus x y
    transSugarAlg (Gt x y) = PGt x y
    transSugarAlg (Or x y) = POr x y
    transSugarAlg (Impl x y) = PImpl x y

class TransHOAS f where
    transHOASAlg :: Alg f HExpr

transHOAS :: (ExpFunctor f, TransHOAS f) => Term f -> HExpr
transHOAS = cataExp transHOASAlg

instance (TransHOAS f, TransHOAS g) => TransHOAS (f :+: g) where
    transHOASAlg (Inl v) = transHOASAlg v
    transHOASAlg (Inr v) = transHOASAlg v

instance TransHOAS Value where
    transHOASAlg (VInt i) = HInt i
    transHOASAlg (VBool b) = HBool b
    transHOASAlg (VPair x y) = HPair x y

instance TransHOAS Op where
    transHOASAlg (Plus x y) = HPlus x y
    transHOASAlg (Mult x y) = HMult x y
    transHOASAlg (If b x y) = HIf b x y
    transHOASAlg (Lt x y) = HLt x y
    transHOASAlg (And x y) = HAnd x y
    transHOASAlg (Not x) = HNot x
    transHOASAlg (Proj p x) = HProj (ptrans p) x
        where ptrans ProjLeft = SProjLeft
              ptrans ProjRight = SProjRight
    transHOASAlg (Eq x y) = HEq x y

instance TransHOAS Lam where
    transHOASAlg (Lam f) = HLam f

instance TransHOAS App where
    transHOASAlg (App x y) = HApp x y