{-# LANGUAGE TypeSynonymInstances, TemplateHaskell, DeriveDataTypeable,
  FlexibleInstances #-}
module Param.DataTypes.Standard 
    (
     module Param.DataTypes.Standard,
     module Param.DataTypes 
    ) where

import Param.DataTypes
import Data.Derive.NFData
import Data.DeriveTH
import Data.Data
import Control.DeepSeq

-- base values

data VType = VTInt
           | VTBool
           | VTPair VType VType
           | VTFun VType VType
             deriving (Eq,Typeable,Data)

data SExpr = SInt Int
           | SBool Bool
           | SPair SExpr SExpr
           | SFun (SExpr -> SExpr)
             deriving (Typeable,Data)

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
           | OLam (OExpr -> OExpr)
           | OApp OExpr OExpr
             deriving (Typeable,Data)

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
           | PLam (PExpr -> PExpr)
           | PApp PExpr PExpr
           | PLet PExpr (PExpr -> PExpr)
             deriving (Typeable,Data)

instance NFData (SExpr -> SExpr) where
    rnf f = f `seq` ()

instance NFData (OExpr -> OExpr) where
    rnf f = f `seq` ()

instance NFData (PExpr -> PExpr) where
    rnf f = f `seq` ()

$(derives [makeNFData] [''SProj,''SExpr,''OExpr,''PExpr,''VType])