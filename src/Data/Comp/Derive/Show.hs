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
     makeShowF,
     ShowConstr(..),
     makeShowConstr
    ) where

import Data.Comp.Derive.Utils
import Language.Haskell.TH

{-| Signature printing. An instance @ShowF f@ gives rise to an instance
  @Show (Term f)@. -}
class ShowF f where
    showF :: f String -> String

showCon :: String -> [String] -> String
showCon con [] = con
showCon con args = "(" ++ con ++ " " ++ unwords args ++ ")"

{-| Derive an instance of 'ShowF' for a type constructor of any first-order kind
  taking at least one argument. -}
makeShowF :: Name -> Q [Dec]
makeShowF fname = do
  Just (DataInfo _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = map (VarT . tyVarBndrName) (init args)
      complType = foldl AppT (ConT name) argNames
      preCond = map (mkClassP ''Show . (: [])) argNames
      classType = AppT (ConT ''ShowF) complType
  constrs' <- mapM normalConExp constrs
  showFDecl <- funD 'showF (showFClauses fArg constrs')
  return [mkInstanceD preCond classType [showFDecl]]
      where showFClauses fArg = map (genShowFClause fArg)
            filterFarg fArg ty x = (fArg == ty, varE x)
            mkShow :: (Bool, ExpQ) -> ExpQ
            mkShow (isFArg, var)
                | isFArg = var
                | otherwise = [| show $var |]
            genShowFClause fArg (constr, args, gadtTy) = do
              let n = length args
              varNs <- newNames n "x"
              let pat = ConP constr [] $ map VarP varNs
                  allVars = zipWith (filterFarg (getUnaryFArg fArg gadtTy)) args varNs
                  shows = listE $ map mkShow allVars
                  conName = nameBase constr
              body <- [|showCon conName $shows|]
              return $ Clause [pat] (NormalB body) []

{-| Constructor printing. -}
class ShowConstr f where
    showConstr :: f a -> String

showCon' :: String -> [String] -> String
showCon' con args = unwords $ con : filter (not.null) args

{-| Derive an instance of 'showConstr' for a type constructor of any first-order kind
  taking at least one argument. -}
makeShowConstr :: Name -> Q [Dec]
makeShowConstr fname = do
  Just (DataInfo _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = map (VarT . tyVarBndrName) (init args)
      complType = foldl AppT (ConT name) argNames
      preCond = map (mkClassP ''Show . (: [])) argNames
      classType = AppT (ConT ''ShowConstr) complType
  constrs' <- mapM normalConExp constrs
  showConstrDecl <- funD 'showConstr (showConstrClauses fArg constrs')
  return [mkInstanceD preCond classType [showConstrDecl]]
      where showConstrClauses fArg = map (genShowConstrClause fArg)
            filterFarg fArg ty x = (fArg == ty, varE x)
            mkShow :: (Bool, ExpQ) -> ExpQ
            mkShow (isFArg, var)
                | isFArg = [| "" |]
                | otherwise = [| show $var |]
            genShowConstrClause fArg (constr, args, gadtTy) = do
              let n = length args
              varNs <- newNames n "x"
              let pat = ConP constr [] $ map VarP varNs
                  allVars = zipWith (filterFarg (getUnaryFArg fArg gadtTy)) args varNs
                  shows = listE $ map mkShow allVars
                  conName = nameBase constr
              body <- [|showCon' conName $shows|]
              return $ Clause [pat] (NormalB body) []
