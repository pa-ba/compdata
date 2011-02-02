{-# LANGUAGE TypeSynonymInstances, TemplateHaskell, DeriveDataTypeable #-}
module DataTypes.Standard 
    ( module DataTypes.Standard,
      module DataTypes 
    ) where

import DataTypes
import Data.Derive.NFData
import Data.DeriveTH
import Data.Data
import Control.DeepSeq

-- base values

data VType = VTInt
           | VTBool
           | VTPair VType VType
             deriving (Eq,Typeable,Data)

data SExpr = SInt Int
           | SBool Bool
           | SPair SExpr SExpr
             deriving (Eq,Typeable,Data)

data SProj = SProjLeft | SProjRight
             deriving (Eq,Typeable,Data)

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
             deriving (Eq,Typeable,Data)

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
             deriving (Eq,Typeable,Data)

data VHType = VHTInt
            | VHTBool
            | VHTPair VType VType
            | VHTFun VType VType
              deriving (Eq,Typeable,Data)

data HExpr = HInt Int
           | HBool Bool
           | HPair HExpr HExpr
           | HPlus HExpr HExpr
           | HMult HExpr HExpr
           | HIf HExpr HExpr HExpr
           | HEq HExpr HExpr
           | HLt HExpr HExpr
           | HAnd HExpr HExpr
           | HNot HExpr
           | HProj SProj HExpr
           | HApp HExpr HExpr
           | HLam (HExpr -> HExpr)
             deriving (Typeable,Data)

data HSExpr = HSInt Int
            | HSBool Bool
            | HSPair HSExpr HSExpr
            | HSLam (HExpr -> HSExpr) -- Nasty dependency with HExpr!
              deriving (Typeable,Data)

instance NFData HExpr where
    rnf (HInt n) = rnf n `seq` ()
    rnf (HBool b) = rnf b `seq` ()
    rnf (HPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HPlus e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HMult e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HIf e1 e2 e3) = rnf e1 `seq` rnf e2 `seq` rnf e3 `seq` ()
    rnf (HEq e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HLt e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HAnd e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HNot e) = rnf e `seq` ()
    rnf (HProj e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HApp e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HLam e) = e `seq` ()

instance NFData HSExpr where
    rnf (HSInt n) = rnf n `seq` ()
    rnf (HSBool b) = rnf b `seq` ()
    rnf (HSPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HSLam e) = e `seq` ()

instance Eq HSExpr where
    (==) (HSInt n1) (HSInt n2) = n1 == n2
    (==) (HSBool b1) (HSBool b2) = b1 == b2
    (==) (HSPair e1 e2) (HSPair e3 e4) = e1 == e3 && e2 == e4
    (==) _ _ = False

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

$(derives [makeNFData] [''SProj,''SExpr,''OExpr,''PExpr,''VType])