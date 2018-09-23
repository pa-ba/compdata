{-# LANGUAGE TypeSynonymInstances, TemplateHaskell, DeriveDataTypeable,
DeriveGeneric, DeriveAnyClass #-}
module DataTypes.Standard 
    ( module DataTypes.Standard,
      module DataTypes 
    ) where

import GHC.Generics (Generic)

import DataTypes
import Data.Data
import Control.DeepSeq

-- base values

data VType = VTInt
           | VTBool
           | VTPair VType VType
             deriving (Eq,Typeable,Data, Generic, NFData)

data SExpr = SInt Int
           | SBool Bool
           | SPair SExpr SExpr
             deriving (Eq,Typeable,Data, Generic, NFData)

data SProj = SProjLeft | SProjRight
             deriving (Eq,Typeable,Data, Generic, NFData)

data OExpr = OInt Int
           | OBool Bool
           | OPair OExpr OExpr
           | OPlus OExpr OExpr
           | OMult OExpr OExpr
           | OIf OExpr OExpr OExpr
           | OEq OExpr OExpr
           | OLt OExpr OExpr
           | OAnd OExpr OExpr
           | ONot OExpr
           | OProj SProj OExpr
             deriving (Eq,Typeable,Data, Generic, NFData)

data PExpr = PInt Int
           | PBool Bool
           | PPair PExpr PExpr
           | PPlus PExpr PExpr
           | PMult PExpr PExpr
           | PIf PExpr PExpr PExpr
           | PEq PExpr PExpr
           | PLt PExpr PExpr
           | PAnd PExpr PExpr
           | PNot PExpr
           | PProj SProj PExpr
           | PNeg PExpr
           | PMinus PExpr PExpr
           | PGt PExpr PExpr
           | POr PExpr PExpr
           | PImpl PExpr PExpr
             deriving (Eq,Typeable,Data, Generic, NFData)

data VHType = VHTInt
            | VHTBool
            | VHTPair VType VType
            | VHTFun VType VType
              deriving (Eq,Typeable,Data, Generic, NFData)

showBinOp :: String -> String -> String -> String
showBinOp op x y = "("++ x ++ op ++ y ++ ")"

instance Show SExpr where
    show (SInt i) = show i
    show (SBool b) = show b
    show (SPair x y) = showBinOp "," (show x) (show y)

instance Show OExpr where
    show (OInt i) = show i
    show (OBool b) = show b
    show (OPair x y) = showBinOp "," (show x) (show y)
    show (OPlus x y) = showBinOp "+" (show x) (show y)
    show (OMult x y) = showBinOp "*" (show x) (show y)
    show (OIf b x y) = "if " ++ show b ++ " then " ++ show x ++ " else " ++ show y ++ " fi"
    show (OEq x y) = showBinOp "==" (show x) (show y)
    show (OLt x y) = showBinOp "<" (show x) (show y)
    show (OAnd x y) = showBinOp "&&" (show x) (show y)
    show (ONot x) = "~" ++ (show x)
    show (OProj SProjLeft x) = (show x) ++ "!0"
    show (OProj SProjRight x) = (show x) ++ "!1"

instance Show VType where 
    show VTInt = "Int"
    show VTBool = "Bool"
    show (VTPair x y) = "(" ++ show x ++ "," ++ show y ++ ")"
