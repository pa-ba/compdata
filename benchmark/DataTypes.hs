{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module DataTypes where

import Data.ALaCarte.Derive
import Data.ALaCarte
import Data.ALaCarte.Show

import Control.Monad hiding (sequence_)
import Prelude hiding (sequence_)

-- base values

type ValueExpr = Term Value
type ExprSig = Value :+: Op
type Expr = Term ExprSig
type SugarSig = Value :+: Op :+: Sugar
type SugarExpr = Term SugarSig
type BaseType = Term ValueT

type Err = Either String

instance Monad Err where
    return = Right
    e >>= f = case e of 
                Left m -> Left m
                Right x -> f x
    fail  = Left

data ValueT e = TInt
              | TBool
              | TPair e e
          deriving (Eq)

data Value e = VInt Int
             | VBool Bool
             | VPair e e
          deriving (Eq)

data Proj = ProjLeft | ProjRight
          deriving (Eq)

data Op e = Plus e e
          | Mult e e
          | If e e e
          | Eq e e
          | Lt e e
          | And e e
          | Not e
          | Proj Proj e
          deriving (Eq)

data Sugar e = Neg e
             | Minus e e
             | Gt e e
             | Or e e
             | Impl e e
          deriving (Eq)



$(derive [instanceFunctor, instanceFoldable, instanceTraversable, instanceEqF, instanceNFDataF, smartConstructors] [''Value, ''Op, ''Sugar, ''ValueT])


showBinOp :: String -> String -> String -> String
showBinOp op x y = "("++ x ++ op ++ y ++ ")"

instance ShowF Value where
    showF (VInt i) = show i
    showF (VBool b) = show b
    showF (VPair x y) = showBinOp "," x y


instance ShowF Op where
    showF (Plus x y) = showBinOp "+" x y
    showF (Mult x y) = showBinOp "*" x y
    showF (If b x y) = "if " ++ b ++ " then " ++ x ++ " else " ++ y ++ " fi"
    showF (Eq x y) = showBinOp "==" x y
    showF (Lt x y) = showBinOp "<" x y
    showF (And x y) = showBinOp "&&" x y
    showF (Not x) = "~" ++ x
    showF (Proj ProjLeft x) = x ++ "!0"
    showF (Proj ProjRight x) = x ++ "!1"

instance ShowF ValueT where 
    showF TInt = "Int"
    showF TBool = "Bool"
    showF (TPair x y) = "(" ++ x ++ "," ++ y ++ ")"
