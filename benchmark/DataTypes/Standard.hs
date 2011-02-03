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

-- Call by name, HOAS
data CBNHExpr = CBNHInt Int
           | CBNHBool Bool
           | CBNHPair CBNHExpr CBNHExpr
           | CBNHPlus CBNHExpr CBNHExpr
           | CBNHMult CBNHExpr CBNHExpr
           | CBNHIf CBNHExpr CBNHExpr CBNHExpr
           | CBNHEq CBNHExpr CBNHExpr
           | CBNHLt CBNHExpr CBNHExpr
           | CBNHAnd CBNHExpr CBNHExpr
           | CBNHNot CBNHExpr
           | CBNHProj SProj CBNHExpr
           | CBNHApp CBNHExpr CBNHExpr
           | CBNHLam (CBNHExpr -> CBNHExpr)
             deriving (Typeable,Data)

data CBNHSExpr = CBNHSInt Int
            | CBNHSBool Bool
            | CBNHSPair CBNHSExpr CBNHSExpr
            | CBNHSLam (CBNHExpr -> CBNHSExpr) -- Nasty dependency with CBNHExpr!
              deriving (Typeable,Data)

instance NFData CBNHExpr where
    rnf (CBNHInt n) = rnf n `seq` ()
    rnf (CBNHBool b) = rnf b `seq` ()
    rnf (CBNHPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHPlus e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHMult e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHIf e1 e2 e3) = rnf e1 `seq` rnf e2 `seq` rnf e3 `seq` ()
    rnf (CBNHEq e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHLt e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHAnd e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHNot e) = rnf e `seq` ()
    rnf (CBNHProj e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHApp e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHLam e) = e `seq` ()

instance NFData CBNHSExpr where
    rnf (CBNHSInt n) = rnf n `seq` ()
    rnf (CBNHSBool b) = rnf b `seq` ()
    rnf (CBNHSPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBNHSLam e) = e `seq` ()

instance Eq CBNHSExpr where
    (==) (CBNHSInt n1) (CBNHSInt n2) = n1 == n2
    (==) (CBNHSBool b1) (CBNHSBool b2) = b1 == b2
    (==) (CBNHSPair e1 e2) (CBNHSPair e3 e4) = e1 == e3 && e2 == e4
    (==) _ _ = False


-- Call by value, HOAS
data CBVHExpr = CBVHInt Int
           | CBVHBool Bool
           | CBVHPair CBVHExpr CBVHExpr
           | CBVHPlus CBVHExpr CBVHExpr
           | CBVHMult CBVHExpr CBVHExpr
           | CBVHIf CBVHExpr CBVHExpr CBVHExpr
           | CBVHEq CBVHExpr CBVHExpr
           | CBVHLt CBVHExpr CBVHExpr
           | CBVHAnd CBVHExpr CBVHExpr
           | CBVHNot CBVHExpr
           | CBVHProj SProj CBVHExpr
           | CBVHApp CBVHExpr CBVHExpr
           | CBVHLam (CBVHSExpr -> CBVHExpr) -- Nasty dependency with CBVHSExpr!
           | CBVHVal CBVHSExpr -- Nasty dependency with CBVHSExpr!
             deriving (Typeable,Data)

data CBVHSExpr = CBVHSInt Int
               | CBVHSBool Bool
               | CBVHSPair CBVHSExpr CBVHSExpr
               | CBVHSLam (CBVHSExpr -> CBVHSExpr)
              deriving (Typeable,Data)

instance NFData CBVHExpr where
    rnf (CBVHInt n) = rnf n `seq` ()
    rnf (CBVHBool b) = rnf b `seq` ()
    rnf (CBVHPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHPlus e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHMult e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHIf e1 e2 e3) = rnf e1 `seq` rnf e2 `seq` rnf e3 `seq` ()
    rnf (CBVHEq e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHLt e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHAnd e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHNot e) = rnf e `seq` ()
    rnf (CBVHProj e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHApp e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHLam e) = e `seq` ()
    rnf (CBVHVal e) = rnf e `seq` ()

instance NFData CBVHSExpr where
    rnf (CBVHSInt n) = rnf n `seq` ()
    rnf (CBVHSBool b) = rnf b `seq` ()
    rnf (CBVHSPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (CBVHSLam e) = e `seq` ()

instance Eq CBVHSExpr where
    (==) (CBVHSInt n1) (CBVHSInt n2) = n1 == n2
    (==) (CBVHSBool b1) (CBVHSBool b2) = b1 == b2
    (==) (CBVHSPair e1 e2) (CBVHSPair e3 e4) = e1 == e3 && e2 == e4
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