{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.SmartAConstructors
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive smart constructors with annotations for higher-order
-- difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Derive.SmartAConstructors 
    (
     smartAConstructors
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.HDifunctor

import Control.Monad

{-| Derive smart constructors with annotations for a higher-order difunctor. The
 smart constructors are similar to the ordinary constructors, but a
 'injectA . hdimap Var id' is automatically inserted. -}
smartAConstructors :: Name -> Q [Dec]
smartAConstructors fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname (name, args) = do
                let bname = nameBase name
                genSmartConstr' targs tname (mkName $ "iA" ++ bname) name args
              genSmartConstr' targs tname sname name args = do
                varNs <- newNames args "x"
                varPr <- newName "_p"
                let pats = map varP (varPr : varNs)
                    vars = map varE varNs
                    val = appE [|injectA $(varE varPr)|] $
                          appE [|inj . hdimap Var id|] $ foldl appE (conE name) vars
                    function = [funD sname [clause pats (normalB [|Term $val|]) []]]
                sequence function