{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, TypeOperators, ScopedTypeVariables,
  TypeSynonymInstances #-}

module Param.DataTypes.Transform where

import Data.Comp.Param
import Param.DataTypes.Standard as S
import Param.DataTypes.Comp

class TransSugar f where
    transSugarAlg :: Alg f PExpr

transSugar :: (Difunctor f, TransSugar f) => Term f -> PExpr
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

instance TransSugar Lam where
    transSugarAlg (Lam f) = PLam f
    transSugarAlg (App x y) = PApp x y

instance TransSugar Sugar where
    transSugarAlg (Neg x) = PNeg x
    transSugarAlg (Minus x y) = PMinus x y
    transSugarAlg (Gt x y) = PGt x y
    transSugarAlg (Or x y) = POr x y
    transSugarAlg (Impl x y) = PImpl x y

instance TransSugar SugarLet where
    transSugarAlg (Let x y) = PLet x y


class TransCore f where
    transCoreAlg :: Alg f OExpr

transCore :: (Difunctor f, TransCore f) => Term f -> OExpr
transCore = cata transCoreAlg


instance (TransCore f, TransCore g) => TransCore (f :+: g) where
    transCoreAlg (Inl v) = transCoreAlg v
    transCoreAlg (Inr v) = transCoreAlg v

instance TransCore Value where
    transCoreAlg (VInt i) = OInt i
    transCoreAlg (VBool b) = OBool b
    transCoreAlg (VPair x y) = OPair x y

instance TransCore Op where
    transCoreAlg (Plus x y) = OPlus x y
    transCoreAlg (Mult x y) = OMult x y
    transCoreAlg (If b x y) = OIf b x y
    transCoreAlg (Lt x y) = OLt x y
    transCoreAlg (And x y) = OAnd x y
    transCoreAlg (Not x) = ONot x
    transCoreAlg (Proj p x) = OProj (ptrans p) x
        where ptrans ProjLeft = SProjLeft
              ptrans ProjRight = SProjRight
    transCoreAlg (Eq x y) = OEq x y

instance TransCore Lam where
    transCoreAlg (Lam f) = OLam f
    transCoreAlg (App x y) = OApp x y

class TransVal f where
    transValAlg :: Alg f SExpr

transVal :: (Difunctor f, TransVal f) => Term f -> SExpr
transVal = cata transValAlg


instance (TransVal f, TransVal g) => TransVal (f :+: g) where
    transValAlg (Inl v) = transValAlg v
    transValAlg (Inr v) = transValAlg v

instance TransVal Value where
    transValAlg (VInt i) = SInt i
    transValAlg (VBool b) = SBool b
    transValAlg (VPair x y) = SPair x y

instance TransVal Fun where
    transValAlg (Fun f) = SFun f

class TransType f where
    transTypeAlg :: Alg f VType

transType :: (Difunctor f, TransType f) => Term f -> VType
transType = cata transTypeAlg


instance (TransType f, TransType g) => TransType (f :+: g) where
    transTypeAlg (Inl v) = transTypeAlg v
    transTypeAlg (Inr v) = transTypeAlg v

instance TransType ValueT where
    transTypeAlg TInt = VTInt
    transTypeAlg TBool = VTBool
    transTypeAlg (TPair x y) = VTPair x y
    transTypeAlg (TFun x y) = VTFun x y