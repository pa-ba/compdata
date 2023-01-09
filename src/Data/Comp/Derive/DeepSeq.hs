{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.DeepSeq
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @DeepSeq@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.DeepSeq
    (
     NFDataF(..),
     makeNFDataF
    ) where


import Control.DeepSeq
import Data.Comp.Derive.Utils
import Language.Haskell.TH

{-| Signature normal form. An instance @NFDataF f@ gives rise to an instance
  @NFData (Term f)@. -}
class NFDataF f where
    rnfF :: NFData a => f a -> ()

{-| Derive an instance of 'NFDataF' for a type constructor of any first-order
  kind taking at least one argument. -}
makeNFDataF :: Name -> Q [Dec]
makeNFDataF fname = do
  Just (DataInfo _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let argNames = map (VarT . tyVarBndrName) (init args)
      complType = foldl AppT (ConT name) argNames
      preCond = map (mkClassP ''NFData . (: [])) argNames
      classType = AppT (ConT ''NFDataF) complType
  constrs' <- mapM normalConExp constrs
  rnfFDecl <- funD 'rnfF (rnfFClauses constrs')
  return [mkInstanceD preCond classType [rnfFDecl]]
      where rnfFClauses = map genRnfFClause
            genRnfFClause (constr, args,_) = do
              let n = length args
              varNs <- newNames n "x"
#if __GLASGOW_HASKELL__ < 900
              let pat = ConP constr $ map VarP varNs
#else
              let pat = ConP constr [] $ map VarP varNs
#endif
                  allVars = map varE varNs
              body <- foldr (\ x y -> [|rnf $x `seq` $y|]) [| () |] allVars
              return $ Clause [pat] (NormalB body) []
