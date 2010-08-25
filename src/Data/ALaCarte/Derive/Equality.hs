{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, FlexibleContexts #-}
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
     deriveEqF,
     deriveEqFs,
    ) where

import Data.ALaCarte.Derive.Utils
import Language.Haskell.TH hiding (Cxt, match)
import Control.Monad

import Data.List


{-|
  Functor type class that provides an 'Eq' instance for the corresponding
  term type class.
-}
class EqF f where
    {-| This function is supposed to implement equality of values of
      type @f a@ modulo the equality of @a@ itself. If two functorial values
      are equal in this sense, 'eqMod' returns a 'Just' value containing a
      list of pairs consisting of corresponding components of the two
      functorial values. -}

    eqMod :: f a -> f b -> Maybe [(a,b)]

    eqF :: Eq a => f a -> f a -> Bool
    eqF x y = maybe
                False
                (all (uncurry (==)))
                (eqMod x y)

                             


{-| This function generates an instance declaration of class
'EqF' for a each of the type constructor given in the argument
list. -}

deriveEqFs :: [Name] -> Q [Dec]
deriveEqFs = liftM concat . mapM deriveEqF

{-| This function generates an instance declaration of class 'EqF' for
a type constructor of any first-order kind taking at least one
argument. The implementation is not capable of deriving instances for
recursive data types. -}

deriveEqF :: Name -> Q [Dec]
deriveEqF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      preCond = map (ClassP ''Eq . (: [])) argNames
      classType = AppT (ConT ''EqF) complType
  eqFDecl <- funD 'eqF  (eqFClauses constrs)
  eqModDecl <- funD 'eqMod  (eqModClauses fArg constrs)
  return $ [InstanceD preCond classType [eqModDecl, eqFDecl]]
      where eqFClauses constrs = map (genEqClause.abstractConType) constrs
                                   ++ (defEqClause constrs)
            eqModClauses fArg constrs = map (genModClause fArg .normalCon') constrs
                                        ++ (defModClause constrs)
            filterFarg fArg ty x = (fArg == ty, x)
            defEqClause constrs
                | length constrs  < 2 = []
                | otherwise = [clause [wildP,wildP] (normalB [|False|]) []]
            defModClause constrs
                | length constrs  < 2 = []
                | otherwise = [clause [wildP,wildP] (normalB [|Nothing|]) []]
            genModClause fArg (constr, args) = do 
              let n = length args
              varNs <- newNames n "x"
              varNs' <- newNames n "y"
              let pat = ConP constr $ map VarP varNs
                  pat' = ConP constr $ map VarP varNs'
                  allVars = zipWith (filterFarg fArg) args varNs
                  allVars' = zipWith (filterFarg fArg) args varNs'
                  (fPreVars,rPreVars) = partition fst allVars
                  (fPreVars',rPreVars') = partition fst allVars'
                  fVars = map (VarE . snd) fPreVars
                  fVars' = map (VarE . snd)  fPreVars'
                  rVars = map (VarE . snd) rPreVars
                  rVars' = map (VarE . snd)  rPreVars'
                  mkMod x y = let (x',y') = (return x,return y)
                             in [| ($x', $y')|]
                  mods = listE $ zipWith mkMod fVars fVars'
                  mkEq x y = let (x',y') = (return x,return y)
                             in [| $x' == $y'|]
                  eqs = listE $ zipWith mkEq rVars rVars'
              body <- [|if and $eqs then Just $mods else Nothing|]
              return $ Clause [pat, pat'] (NormalB body) []
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