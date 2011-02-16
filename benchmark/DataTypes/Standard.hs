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

-- HOAS
data HOASExpr = HOASInt Int
              | HOASBool Bool
              | HOASPair HOASExpr HOASExpr
              | HOASPlus HOASExpr HOASExpr
              | HOASMult HOASExpr HOASExpr
              | HOASIf HOASExpr HOASExpr HOASExpr
              | HOASEq HOASExpr HOASExpr
              | HOASLt HOASExpr HOASExpr
              | HOASAnd HOASExpr HOASExpr
              | HOASNot HOASExpr
              | HOASProj SProj HOASExpr
              | HOASApp HOASExpr HOASExpr
              | HOASLam (HOASSExpr -> HOASExpr) -- Nasty dependency with HOASSExpr!
              | HOASVal HOASSExpr -- Nasty dependency with HOASSExpr!
                deriving (Typeable,Data)

data HOASSExpr = HOASSInt Int
               | HOASSBool Bool
               | HOASSPair HOASSExpr HOASSExpr
               | HOASSLam (HOASSExpr -> HOASSExpr)
                 deriving (Typeable,Data)

instance NFData HOASExpr where
    rnf (HOASInt n) = rnf n `seq` ()
    rnf (HOASBool b) = rnf b `seq` ()
    rnf (HOASPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASPlus e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASMult e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASIf e1 e2 e3) = rnf e1 `seq` rnf e2 `seq` rnf e3 `seq` ()
    rnf (HOASEq e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASLt e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASAnd e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASNot e) = rnf e `seq` ()
    rnf (HOASProj e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASApp e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASLam e) = e `seq` ()
    rnf (HOASVal e) = rnf e `seq` ()

instance NFData HOASSExpr where
    rnf (HOASSInt n) = rnf n `seq` ()
    rnf (HOASSBool b) = rnf b `seq` ()
    rnf (HOASSPair e1 e2) = rnf e1 `seq` rnf e2 `seq` ()
    rnf (HOASSLam e) = e `seq` ()

instance Eq HOASSExpr where
    (==) (HOASSInt n1) (HOASSInt n2) = n1 == n2
    (==) (HOASSBool b1) (HOASSBool b2) = b1 == b2
    (==) (HOASSPair e1 e2) (HOASSPair e3 e4) = e1 == e3 && e2 == e4
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