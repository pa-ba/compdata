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
import Data.Comp.Derive
import DataTypes.Standard as S
import DataTypes.Comp

class TransSugar f where
    transSugarAlg :: Alg f PExpr

transSugar :: (Functor f, TransSugar f) => Term f -> PExpr
transSugar = cata transSugarAlg

$(derive [liftSum] [''TransSugar])

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



class TransCore f where
    transCoreAlg :: Alg f OExpr

transCore :: (Functor f, TransCore f) => Term f -> OExpr
transCore = cata transCoreAlg

$(derive [liftSum] [''TransCore])

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

class TransVal f where
    transValAlg :: Alg f SExpr

transVal :: (Functor f, TransVal f) => Term f -> SExpr
transVal = cata transValAlg

$(derive [liftSum] [''TransVal])

instance TransVal Value where
    transValAlg (VInt i) = SInt i
    transValAlg (VBool b) = SBool b
    transValAlg (VPair x y) = SPair x y

class TransType f where
    transTypeAlg :: Alg f VType

transType :: (Functor f, TransType f) => Term f -> VType
transType = cata transTypeAlg

$(derive [liftSum] [''TransType])

instance TransType ValueT where
    transTypeAlg TInt = VTInt
    transTypeAlg TBool = VTBool
    transTypeAlg (TPair x y) = VTPair x y