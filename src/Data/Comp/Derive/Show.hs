{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Show
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @ShowF@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.Show
    (
     ShowF(..),
     makeShowF
    ) where

import Data.Comp.Derive.Utils
import Language.Haskell.TH

{-| Signature printing. An instance @ShowF f@ gives rise to an instance
  @Show (Term f)@. -}
class ShowF f where
    showF :: f String -> String
             
showConstr :: String -> [String] -> String
showConstr con [] = con
showConstr con args = "(" ++ con ++ " " ++ unwords args ++ ")"

{-| Derive an instance of 'ShowF' for a type constructor of any first-order kind
  taking at least one argument. -}
makeShowF :: Name -> Q [Dec]
makeShowF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Show . (: [])) argNames
      classType = AppT (ConT ''ShowF) complType
  constrs' <- mapM normalConExp constrs
  showFDecl <- funD 'showF (showFClauses fArg constrs')
  return [InstanceD preCond classType [showFDecl]]
      where showFClauses fArg = map (genShowFClause fArg)
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
