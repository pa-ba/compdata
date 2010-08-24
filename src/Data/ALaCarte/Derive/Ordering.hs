{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.Ordering
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- The ordering algebra (orderings on terms).
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Derive.Ordering
    ( OrdF(..),
      compList,
      deriveOrdFs,
      deriveOrdF
    ) where

import Data.ALaCarte.Equality
import Data.ALaCarte.Derive.Utils

import Data.Maybe
import Data.List
import Control.Monad
import Language.Haskell.TH hiding (Cxt)

{-|
  Functor type class that provides an 'Eq' instance for the corresponding
  term type class.
-}
class EqF f => OrdF f where
    compAlg :: Ord a => f a -> f a -> Ordering

    
compList :: [Ordering] -> Ordering
compList = fromMaybe EQ . find (/= EQ)

deriveOrdFs :: [Name] -> Q [Dec]
deriveOrdFs = liftM concat . mapM deriveOrdF

{-| This function generates an instance declaration of class
'OrdF' for a type constructor of any first-order kind taking at
least one argument. -}

deriveOrdF :: Name -> Q [Dec]
deriveOrdF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Ord . (: [])) argNames
      classType = AppT (ConT ''OrdF) complType
  eqAlgDecl <- funD 'compAlg  (compAlgClauses constrs)
  return $ [InstanceD preCond classType [eqAlgDecl]]
      where compAlgClauses [] = []
            compAlgClauses constrs = 
                let constrs' = map abstractConType constrs `zip` [1..]
                    constPairs = [(x,y)| x<-constrs', y <- constrs']
                in map genClause constPairs
            genClause ((c,n),(d,m))
                | n == m = genEqClause c
                | n < m = genLtClause c d
                | otherwise = genGtClause c d
            genEqClause (constr, n) = do 
              varNs <- newNames n "x"
              varNs' <- newNames n "y"
              let pat = ConP constr $ map VarP varNs
                  pat' = ConP constr $ map VarP varNs'
                  vars = map VarE varNs
                  vars' = map VarE varNs'
                  mkEq x y = let (x',y') = (return x,return y)
                             in [| compare $x' $y'|]
                  eqs = listE $ zipWith mkEq vars vars'
              body <- [|compList $eqs|]
              return $ Clause [pat, pat'] (NormalB body) []
            genLtClause (c, _) (d, _) = clause [recP c [], recP d []] (normalB [| LT |]) []
            genGtClause (c, _) (d, _) = clause [recP c [], recP d []] (normalB [| GT |]) []