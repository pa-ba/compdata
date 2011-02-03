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

class TransCBNHOAS f where
    transCBNHOASAlg :: Alg f CBNHExpr

transCBNHOAS :: (ExpFunctor f, TransCBNHOAS f) => Term f -> CBNHExpr
transCBNHOAS = cataExp transCBNHOASAlg

instance (TransCBNHOAS f, TransCBNHOAS g) => TransCBNHOAS (f :+: g) where
    transCBNHOASAlg (Inl v) = transCBNHOASAlg v
    transCBNHOASAlg (Inr v) = transCBNHOASAlg v

instance TransCBNHOAS Value where
    transCBNHOASAlg (VInt i) = CBNHInt i
    transCBNHOASAlg (VBool b) = CBNHBool b
    transCBNHOASAlg (VPair x y) = CBNHPair x y

instance TransCBNHOAS Op where
    transCBNHOASAlg (Plus x y) = CBNHPlus x y
    transCBNHOASAlg (Mult x y) = CBNHMult x y
    transCBNHOASAlg (If b x y) = CBNHIf b x y
    transCBNHOASAlg (Lt x y) = CBNHLt x y
    transCBNHOASAlg (And x y) = CBNHAnd x y
    transCBNHOASAlg (Not x) = CBNHNot x
    transCBNHOASAlg (Proj p x) = CBNHProj (ptrans p) x
        where ptrans ProjLeft = SProjLeft
              ptrans ProjRight = SProjRight
    transCBNHOASAlg (Eq x y) = CBNHEq x y

instance TransCBNHOAS Lam where
    transCBNHOASAlg (Lam f) = CBNHLam f

instance TransCBNHOAS App where
    transCBNHOASAlg (App x y) = CBNHApp x y


class TransCBVHOAS f where
    transCBVHOASAlg :: Alg f CBVHExpr

transCBVHOAS :: (ExpFunctor f, TransCBVHOAS f) => Term f -> CBVHExpr
transCBVHOAS = cataExp transCBVHOASAlg

instance (TransCBVHOAS f, TransCBVHOAS g) => TransCBVHOAS (f :+: g) where
    transCBVHOASAlg (Inl v) = transCBVHOASAlg v
    transCBVHOASAlg (Inr v) = transCBVHOASAlg v

instance TransCBVHOAS Value where
    transCBVHOASAlg (VInt i) = CBVHInt i
    transCBVHOASAlg (VBool b) = CBVHBool b
    transCBVHOASAlg (VPair x y) = CBVHPair x y

instance TransCBVHOAS Op where
    transCBVHOASAlg (Plus x y) = CBVHPlus x y
    transCBVHOASAlg (Mult x y) = CBVHMult x y
    transCBVHOASAlg (If b x y) = CBVHIf b x y
    transCBVHOASAlg (Lt x y) = CBVHLt x y
    transCBVHOASAlg (And x y) = CBVHAnd x y
    transCBVHOASAlg (Not x) = CBVHNot x
    transCBVHOASAlg (Proj p x) = CBVHProj (ptrans p) x
        where ptrans ProjLeft = SProjLeft
              ptrans ProjRight = SProjRight
    transCBVHOASAlg (Eq x y) = CBVHEq x y

instance TransCBVHOAS Lam where
    transCBVHOASAlg (Lam f) = CBVHLam $ f . CBVHVal

instance TransCBVHOAS App where
    transCBVHOASAlg (App x y) = CBVHApp x y