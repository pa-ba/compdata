{-# LANGUAGE ImplicitParams, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.Signature
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Derive.SmartConstructors 
    (smartConstructors) where



import Language.Haskell.TH
import Data.ALaCarte.Derive.Utils
import Data.ALaCarte.Sum
import Data.ALaCarte.Term

import Data.Char
import Control.Monad


smartConstructors :: Name -> Q [Dec]
smartConstructors fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname (name, args) = do
                let bname = nameBase name
                case bname of
                  x : xs
                      | isUpper x -> genSmartConstr' targs tname (mkName $ toLower x : xs) name args
                  _  -> do
                    report False $ "cannot make constructor '" ++ bname
                        ++ "' into a smart constructor"
                    return []
              genSmartConstr' targs tname sname name args = do
                varNs <- newNames args "x"
                let pats = map varP varNs
                    vars = map varE varNs
                    val = foldl appE (conE name) vars
                    sig = genSig targs tname sname args
                    function = [funD sname [clause pats (normalB [|inject $val|]) []]]
                sequence $ sig ++ function
              genSig targs tname sname 0 = (:[]) $ do
                fvar <- newName "f"
                let targs' = init targs
                    vars = fvar:targs'
                    f = varT fvar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = classP ''(:<:) [ftype, f]
                    typ = appT (conT ''Term) f
                    typeSig = forallT (map PlainTV vars) (sequence [constr]) typ
                sigD sname typeSig
              genSig _ _ _ _ = []