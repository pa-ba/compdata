{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.DeepSeq
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.DeepSeq
    ( NFDataF(..),
      instanceNFDataF
    ) where


import Control.DeepSeq
import Data.Comp.Derive.Utils
import Language.Haskell.TH
import Data.Maybe


class NFDataF f where
    rnfF :: NFData a => f a -> ()

instanceNFDataF :: Name -> Q [Dec]
instanceNFDataF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''NFData . (: [])) argNames
      classType = AppT (ConT ''NFDataF) complType
  rnfFDecl <- funD 'rnfF (rnfFClauses fArg constrs)
  return $ [InstanceD preCond classType [rnfFDecl]]
      where rnfFClauses fArg constrs = map (genRnfFClause fArg .normalCon') constrs
            filterFarg excl x
                | excl = Nothing
                | otherwise = Just $ varE x
            mkPat True _ = WildP
            mkPat False x = VarP x
            genRnfFClause fArg (constr, args) = do 
              let isFargs = map (==fArg) args
                  n = length args
              varNs <- newNames n "x"
              let pat = ConP constr $ zipWith mkPat isFargs varNs
                  allVars = catMaybes $ zipWith filterFarg isFargs varNs
              body <- foldr (\ x y -> [|rnf $x `seq` $y|]) [| () |] allVars
              return $ Clause [pat] (NormalB body) []
