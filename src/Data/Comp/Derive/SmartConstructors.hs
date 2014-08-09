{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Signature
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive smart constructors.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.SmartConstructors
    (
     smartConstructors
    ) where

import Control.Monad
import Data.Comp.Derive.Utils
import Data.Comp.Sum
import Data.Comp.Term
import Language.Haskell.TH hiding (Cxt)

{-| Derive smart constructors for a type constructor of any first-order kind
 taking at least one argument. The smart constructors are similar to the
 ordinary constructors, but an 'inject' is automatically inserted. -}
smartConstructors :: Name -> Q [Dec]
smartConstructors fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname (name, args) = do
                let bname = nameBase name
                genSmartConstr' targs tname (mkName $ 'i' : bname) name args
              genSmartConstr' targs tname sname name args = do
                varNs <- newNames args "x"
                let pats = map varP varNs
                    vars = map varE varNs
                    val = foldl appE (conE name) vars
                    sig = genSig targs tname sname args
                    function = [funD sname [clause pats (normalB [|inject $val|]) []]]
                sequence $ sig ++ function
              genSig targs tname sname 0 = (:[]) $ do
                let fvar = mkName "f"
                    hvar = mkName "h"
                    avar = mkName "a"
                    targs' = init targs
                    vars = fvar:hvar:avar:targs'
                    f = varT fvar
                    h = varT hvar
                    a = varT avar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = classP ''(:<:) [ftype, f]
                    typ = foldl appT (conT ''Cxt) [h, f, a]
                    typeSig = forallT (map PlainTV vars) (sequence [constr]) typ
                sigD sname typeSig
              genSig _ _ _ _ = []
