{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.Show
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Derive.Show
    ( ShowF(..),
      instanceShowF
    ) where

import Data.ALaCarte.Derive.Utils
import Language.Haskell.TH
import Data.List

class Functor f => ShowF f where
    showF :: f String -> String
             
showConstr :: String -> [String] -> String
showConstr con [] = con
showConstr con args = "(" ++ con ++ " " ++ concat (intersperse " " args) ++ ")"


instanceShowF :: Name -> Q [Dec]
instanceShowF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Show . (: [])) argNames
      classType = AppT (ConT ''ShowF) complType
  showFDecl <- funD 'showF (showFClauses fArg constrs)
  return $ [InstanceD preCond classType [showFDecl]]
      where showFClauses fArg constrs = map (genShowFClause fArg .normalCon') constrs
            filterFarg fArg ty x = (fArg == ty, varE x)
            mkShow (isFArg, var)
                | isFArg = var
                | otherwise = [| show $var |]
            genShowFClause fArg (constr, args) = do 
              let n = length args
              varNs <- newNames n "x"
              let pat = ConP constr $ map VarP varNs
                  allVars = zipWith (filterFarg fArg) args varNs
                  shows = listE $ map mkShow allVars
                  conName = nameBase constr
              body <- [|showConstr conName $shows|]
              return $ Clause [pat] (NormalB body) []
