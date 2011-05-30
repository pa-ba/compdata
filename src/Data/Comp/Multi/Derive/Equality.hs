{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Derive.Equality
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HEqF@.
--
--------------------------------------------------------------------------------
module Data.Comp.Multi.Derive.Equality
    (
     HEqF(..),
     KEq(..),
     makeHEqF
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Multi.Functor
import Language.Haskell.TH hiding (Cxt, match)


class KEq f where
    keq :: f i -> f j -> Bool

{-| Signature equality. An instance @HEqF f@ gives rise to an instance
  @KEq (HTerm f)@. -}
class HEqF f where

    heqF :: KEq g => f g i -> f g j -> Bool


instance KEq f => Eq (f i) where
    (==) = keq

instance Eq a => KEq (K a) where
    keq (K x) (K y) = x == y

instance KEq a => Eq (A a) where
     A x == A y = x `keq`  y

{-| Derive an instance of 'HEqF' for a type constructor of any higher-order
  kind taking at least two arguments. -}
makeHEqF :: Name -> Q [Dec]
makeHEqF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = init args
      argNames = (map (VarT . tyVarBndrName) (init args'))
      ftyp = VarT . tyVarBndrName $ last args'
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Eq . (: [])) argNames
      classType = AppT (ConT ''HEqF) complType
  constrs' <- mapM normalConExp constrs
  eqFDecl <- funD 'heqF  (eqFClauses ftyp constrs constrs')
  return [InstanceD preCond classType [eqFDecl]]
      where eqFClauses ftyp constrs constrs' = map (genEqClause ftyp) constrs'
                                   ++ defEqClause constrs
            filterFarg fArg ty x = (containsType ty fArg, varE x)
            defEqClause constrs
                | length constrs  < 2 = []
                | otherwise = [clause [wildP,wildP] (normalB [|False|]) []]
            genEqClause ftyp (constr, argts) = do 
              let n = length argts
              varNs <- newNames n "x"
              varNs' <- newNames n "y"
              let pat = ConP constr $ map VarP varNs
                  pat' = ConP constr $ map VarP varNs'
                  vars = map VarE varNs
                  vars' = map VarE varNs'
                  mkEq ty x y = let (x',y') = (return x,return y)
                                in if containsType ty ftyp
                                   then [| $x' `keq` $y'|]
                                   else [| $x' == $y'|]
                  eqs = listE $ zipWith3 mkEq argts vars vars'
              body <- if n == 0 
                      then [|True|]
                      else [|and $eqs|]
              return $ Clause [pat, pat'] (NormalB body) []