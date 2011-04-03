{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Derive.SmartPConstructors
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive smart constructors with products for parametric types.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Derive.SmartPConstructors 
    (
     smartPConstructors
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Term
import Data.Comp.Multi.Product
import Control.Monad

{-| Derive smart constructors with products for a type constructor of any
  parametric kind taking at least two arguments. The smart constructors are
  similar to the ordinary constructors, but an 'injectP' is automatically
  inserted. -}
smartPConstructors :: Name -> Q [Dec]
smartPConstructors fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname (name, args) = do
                let bname = nameBase name
                genSmartConstr' targs tname (mkName $ "iP" ++ bname) name args
              genSmartConstr' targs tname sname name args = do
                varNs <- newNames args "x"
                varPr <- newName "_p"
                let pats = map varP (varPr : varNs)
                    vars = map varE varNs
                    val = appE [|injectP $(varE varPr)|] $
                          appE [|inj|] $ foldl appE (conE name) vars
                    function = [funD sname [clause pats (normalB [|Term $val|]) []]]
                sequence function