{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.DeepSeq
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
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
  constrs' <- mapM normalConExp constrs
  rnfFDecl <- funD 'rnfF (rnfFClauses fArg constrs')
  return [InstanceD preCond classType [rnfFDecl]]
      where rnfFClauses fArg = map (genRnfFClause fArg)
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
