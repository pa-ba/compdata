{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Equality
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @EqF@.
--
--------------------------------------------------------------------------------
module Data.Comp.Derive.Equality
    (
     EqF(..),
     instanceEqF
    ) where

import Data.Comp.Derive.Utils
import Language.Haskell.TH hiding (Cxt, match)


{-| Signature equality. An instance @EqF f@ gives rise to an instance
  @Eq (Term f)@. -}
class EqF f where

    eqF :: Eq a => f a -> f a -> Bool

{-| Derive an instance of 'EqF' for a type constructor of any first-order kind
  taking at least one argument. -}
instanceEqF :: Name -> Q [Dec]
instanceEqF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Eq . (: [])) argNames
      classType = AppT (ConT ''EqF) complType
  eqFDecl <- funD 'eqF  (eqFClauses constrs)
  return [InstanceD preCond classType [eqFDecl]]
      where eqFClauses constrs = map (genEqClause.abstractConType) constrs
                                   ++ defEqClause constrs
            filterFarg fArg ty x = (fArg == ty, x)
            defEqClause constrs
                | length constrs  < 2 = []
                | otherwise = [clause [wildP,wildP] (normalB [|False|]) []]
            genEqClause (constr, n) = do 
              varNs <- newNames n "x"
              varNs' <- newNames n "y"
              let pat = ConP constr $ map VarP varNs
                  pat' = ConP constr $ map VarP varNs'
                  vars = map VarE varNs
                  vars' = map VarE varNs'
                  mkEq x y = let (x',y') = (return x,return y)
                             in [| $x' == $y'|]
                  eqs = listE $ zipWith mkEq vars vars'
              body <- if n == 0 
                      then [|True|]
                      else [|and $eqs|]
              return $ Clause [pat, pat'] (NormalB body) []