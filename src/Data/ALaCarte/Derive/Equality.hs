{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.Equality
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- The equality algebra (equality on terms).
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Derive.Equality
    (
     EqF(..),
     instanceEqF
    ) where

import Data.ALaCarte.Derive.Utils
import Language.Haskell.TH hiding (Cxt, match)


{-|
  Functor type class that provides an 'Eq' instance for the corresponding
  term type class.
-}
class EqF f where

    eqF :: Eq a => f a -> f a -> Bool

                             

{-| This function generates an instance declaration of class 'EqF' for
a type constructor of any first-order kind taking at least one
argument. The implementation is not capable of deriving instances for
recursive data types. -}

instanceEqF :: Name -> Q [Dec]
instanceEqF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Eq . (: [])) argNames
      classType = AppT (ConT ''EqF) complType
  eqFDecl <- funD 'eqF  (eqFClauses constrs)
  return $ [InstanceD preCond classType [eqFDecl]]
      where eqFClauses constrs = map (genEqClause.abstractConType) constrs
                                   ++ (defEqClause constrs)
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