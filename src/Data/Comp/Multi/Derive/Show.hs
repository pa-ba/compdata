{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Derive.Show
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @ShowHF@.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Derive.Show
    (
     ShowHF(..),
     KShow(..),
     makeShowHF
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Multi.Functor
import Data.Comp.Multi.Algebra
import Language.Haskell.TH

{-| Signature printing. An instance @ShowHF f@ gives rise to an instance
  @KShow (HTerm f)@. -}
class ShowHF f where
    showHF :: Alg f (K String)
    showHF = K . showHF'
    showHF' :: f (K String) :=> String
    showHF' = unK . showHF

class KShow a where
    kshow :: a i -> K String i

showConstr :: String -> [String] -> String
showConstr con [] = con
showConstr con args = "(" ++ con ++ " " ++ unwords args ++ ")"

{-| Derive an instance of 'ShowHF' for a type constructor of any higher-order
  kind taking at least two arguments. -}
makeShowHF :: Name -> Q [Dec]
makeShowHF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = init args
      fArg = VarT . tyVarBndrName $ last args'
      argNames = (map (VarT . tyVarBndrName) (init args'))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Show . (: [])) argNames
      classType = AppT (ConT ''ShowHF) complType
  constrs' <- mapM normalConExp constrs
  showFDecl <- funD 'showHF (showFClauses fArg constrs')
  return [InstanceD preCond classType [showFDecl]]
      where showFClauses fArg = map (genShowFClause fArg)
            filterFarg fArg ty x = (containsType ty fArg, varE x)
            mkShow (isFArg, var)
                | isFArg = [|unK $var|]
                | otherwise = [| show $var |]
            genShowFClause fArg (constr, args) = do 
              let n = length args
              varNs <- newNames n "x"
              let pat = ConP constr $ map VarP varNs
                  allVars = zipWith (filterFarg fArg) args varNs
                  shows = listE $ map mkShow allVars
                  conName = nameBase constr
              body <- [|K $ showConstr conName $shows|]
              return $ Clause [pat] (NormalB body) []
