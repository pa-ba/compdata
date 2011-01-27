{-# LANGUAGE
  TemplateHaskell,
  FlexibleInstances,
  FlexibleContexts,
  TypeOperators,
  GADTs,
  KindSignatures,
  IncoherentInstances #-}

-- base values

module Multi.DataTypes.ALaCarte where

import Data.ALaCarte.Derive
import Data.ALaCarte.Multi

type ValueExpr = Term Value
type ExprSig = Value :++: Op
type Expr = Term ExprSig
type SugarSig = Value :++: Op :++: Sugar
type SugarExpr = Term SugarSig
type BaseType = Term ValueT

data ValueT e t = TInt
                | TBool
                | TPair (e t) (e t)
          deriving (Eq)

data Value e t where
    VInt :: Int -> Value e Int
    VBool :: Bool -> Value e Bool
    VPair :: e s -> e t -> Value e (s,t)


data Op e t where
    Plus :: e Int -> e Int -> Op e Int
    Mult :: e Int -> e Int -> Op e Int
    If :: e Bool -> e t -> e t -> Op e t
    Lt :: e Int -> e Int -> Op e Bool
    Eq :: e Int -> e Int -> Op e Bool
    And :: e Bool -> e Bool -> Op e Bool
    Not :: e Bool -> Op e Bool
    ProjLeft :: e (s,t) -> Op e s
    ProjRight :: e (s,t) -> Op e t

data Sugar e t where
    Neg  :: e Int -> Sugar e Int
    Minus :: e Int -> e Int -> Sugar e Int
    Gt :: e Int -> e Int -> Sugar e Bool
    Or :: e Bool -> e Bool -> Sugar e Bool
    Impl :: e Bool -> e Bool -> Sugar e Bool

$(derive
  [instanceHFunctor, instanceHFoldable, instanceHTraversable, instanceHEqF, smartMConstructors]
  [''ValueT, ''Value, ''Op, ''Sugar])


showBinOp :: String -> String -> String -> String
showBinOp op x y = "("++ x ++ op ++ y ++ ")"

instance HShowF ValueT where
    hshowF' TInt = "Int"
    hshowF' TBool = "Bool"
    hshowF' (TPair (K x) (K y)) = showBinOp "," x y

instance HShowF Value where
    hshowF' (VInt i) = show i
    hshowF' (VBool b) = show b
    hshowF' (VPair (K x) (K y)) = showBinOp "," x y

instance HShowF Op where
    hshowF' (Plus (K x) (K y)) = showBinOp "+" x y
    hshowF' (Mult (K x) (K y)) = showBinOp "*" x y
    hshowF' (If (K b) (K x) (K y)) = "if " ++ b ++ " then " ++ x ++ " else " ++ y ++ " fi"
    hshowF' (Eq (K x) (K y)) = showBinOp "==" x y
    hshowF' (Lt (K x) (K y)) = showBinOp "<" x y
    hshowF' (And (K x) (K y)) = showBinOp "&&" x y
    hshowF' (Not (K x)) = "~" ++ x
    hshowF' (ProjLeft (K x)) = x ++ "!0"
    hshowF' (ProjRight (K x)) = x ++ "!1"