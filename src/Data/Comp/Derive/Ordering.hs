{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Ordering
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @OrdF@.
--
--------------------------------------------------------------------------------
module Data.Comp.Derive.Ordering
    (
     OrdF(..),
     makeOrdF
    ) where

import Data.Comp.Derive.Equality
import Data.Comp.Derive.Utils

import Data.List
import Data.Maybe
import Language.Haskell.TH hiding (Cxt)

{-| Signature ordering. An instance @OrdF f@ gives rise to an instance
  @Ord (Term f)@. -}
class EqF f => OrdF f where
    compareF :: Ord a => f a -> f a -> Ordering


compList :: [Ordering] -> Ordering
compList = fromMaybe EQ . find (/= EQ)

{-| Derive an instance of 'OrdF' for a type constructor of any first-order kind
  taking at least one argument. -}
makeOrdF :: Name -> Q [Dec]
makeOrdF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let argNames = map (VarT . tyVarBndrName) (init args)
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Ord . (: [])) argNames
      classType = AppT (ConT ''OrdF) complType
  eqAlgDecl <- funD 'compareF  (compareFClauses constrs)
  return [InstanceD preCond classType [eqAlgDecl]]
      where compareFClauses [] = []
            compareFClauses constrs =
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
