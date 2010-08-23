{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Equality
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- The equality algebra (equality on terms).
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Equality
    (
     FunctorEq(..),
     deriveFunctorEq,
     deriveFunctorEqs
    ) where

import Data.ALaCarte
import Data.ALaCarte.Derive
import Language.Haskell.TH hiding (Cxt)
import Control.Monad


{-|
  Functor type class that provides an 'Eq' instance for the corresponding
  term type class.
-}
class FunctorEq f where
    eqAlg :: Eq a => f a -> f a -> Bool

{-|
  'FunctorEq' is propagated through sums.
-}

instance (FunctorEq f, FunctorEq g) => FunctorEq (f :+: g) where
  eqAlg (Inl x) (Inl y) = eqAlg x y
  eqAlg (Inr x) (Inr y) = eqAlg x y
  eqAlg _ _ = False

{-|
  From an 'FunctorEq' functor an 'Eq' instance of the corresponding
  term type can be derived.
-}
instance (FunctorEq f) => FunctorEq (Cxt h f) where
    eqAlg (Term e1) (Term e2) = e1 `eqAlg` e2
    eqAlg (Hole h1) (Hole h2) = h1 == h2
    eqAlg _ _ = False

instance (FunctorEq f, Eq a)  => Eq (Cxt h f a) where
    (==) = eqAlg

deriveFunctorEqs :: [Name] -> Q [Dec]
deriveFunctorEqs = liftM concat . mapM deriveFunctorEq



{-| This function generates an instance declaration of class
'FunctorEq' for a type constructor of any first-order kind taking at
least one argument. -}

deriveFunctorEq :: Name -> Q [Dec]
deriveFunctorEq fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let complType = foldl AppT (ConT name) (map (VarT . tyVarBndrName) (tail args))
      classType = AppT (ConT ''FunctorEq) complType
  eqAlgDecl <- funD 'eqAlg  (eqAlgClauses constrs)
  return $ [InstanceD [] classType [eqAlgDecl]]
      where eqAlgClauses constrs = map (genEqClause.abstractConType) constrs ++ (defClause constrs)
            defClause constrs
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