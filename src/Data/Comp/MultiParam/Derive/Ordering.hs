{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.Ordering
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @OrdHD@.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam.Derive.Ordering
    (
     OrdHD(..),
     instanceOrdHD
    ) where

import Data.Comp.MultiParam.Ordering
import Data.Comp.Derive.Utils

import Data.Maybe
import Data.List
import Language.Haskell.TH hiding (Cxt)
import Control.Monad (liftM)

compList :: [Ordering] -> Ordering
compList = fromMaybe EQ . find (/= EQ)

{-| Derive an instance of 'OrdHD' for a type constructor of any parametric
  kind taking at least three arguments. -}
instanceOrdHD :: Name -> Q [Dec]
instanceOrdHD fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Name = tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Name = tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''OrdHD) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  compareHDDecl <- funD 'compareHD (compareHDClauses coArg conArg constrs')
  return [InstanceD [] classType [compareHDDecl]]
      where compareHDClauses :: Name -> Name -> [(Name,[Type])] -> [ClauseQ]
            compareHDClauses _ _ [] = []
            compareHDClauses coArg conArg constrs = 
                let constrs' = constrs `zip` [1..]
                    constPairs = [(x,y)| x<-constrs', y <- constrs']
                in map (genClause coArg conArg) constPairs
            genClause coArg conArg ((c,n),(d,m))
                | n == m = genEqClause coArg conArg c
                | n < m = genLtClause c d
                | otherwise = genGtClause c d
            genEqClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            genEqClause coArg conArg (constr, args) = do 
              varXs <- newNames (length args) "x"
              varYs <- newNames (length args) "y"
              let patX = ConP constr $ map VarP varXs
              let patY = ConP constr $ map VarP varYs
              body <- eqDBody coArg conArg (zip3 varXs varYs args)
              return $ Clause [patX, patY] (NormalB body) []
            eqDBody :: Name -> Name -> [(Name, Name, Type)] -> ExpQ
            eqDBody coArg conArg x =
                [|liftM compList (sequence $(listE $ map (eqDB coArg conArg) x))|]
            eqDB :: Name -> Name -> (Name, Name, Type) -> ExpQ
            eqDB coArg conArg (x, y, tp)
                | containsType tp (VarT conArg) = [| compareHD $(varE x) $(varE y) |]
                | containsType tp (VarT coArg) = [| pcompare $(varE x) $(varE y) |]
                | otherwise = [| return $ compare $(varE x) $(varE y) |]
            genLtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return LT |]) []
            genGtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return GT |]) []