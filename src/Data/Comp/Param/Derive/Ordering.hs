{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.Ordering
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @OrdD@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Derive.Ordering
    (
     OrdD(..),
     instanceOrdD
    ) where

import Data.Comp.Param.Ordering
import Data.Comp.Derive.Utils

import Data.Maybe
import Data.List
import Language.Haskell.TH hiding (Cxt)
import Control.Monad (liftM)

compList :: [Ordering] -> Ordering
compList = fromMaybe EQ . find (/= EQ)

{-| Derive an instance of 'OrdD' for a type constructor of any parametric
  kind taking at least two arguments. -}
instanceOrdD :: Name -> Q [Dec]
instanceOrdD fname = do
  -- Comments below apply to the example where name = T, args = [a,b,c], and
  -- constrs = [(X,[c]), (Y,[a,c]), (Z,[b -> c])], i.e. the data type
  -- declaration: T a b c = X c | Y a c | Z (b -> c)
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  -- conArg = b (contravariant difunctor argument)
  let conArg :: Name = tyVarBndrName $ last $ init args
  -- argNames = [a]
  let argNames = map (VarT . tyVarBndrName) (init $ init args)
  -- compType = T a
  let complType = foldl AppT (ConT name) argNames
  -- classType = Difunctor (T a)
  let classType = AppT (ConT ''OrdD) complType
  -- constrs' = [(X,[c]), (Y,[a,c]), (Z,[b -> c])]
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  compareDDecl <- funD 'compareD (compareDClauses conArg constrs')
  return [InstanceD [] classType [compareDDecl]]
      where compareDClauses :: Name -> [(Name,[Type])] -> [ClauseQ]
            compareDClauses _ [] = []
            compareDClauses conArg constrs = 
                let constrs' = constrs `zip` [1..]
                    constPairs = [(x,y)| x<-constrs', y <- constrs']
                in map (genClause conArg) constPairs
            genClause conArg ((c,n),(d,m))
                | n == m = genEqClause conArg c
                | n < m = genLtClause c d
                | otherwise = genGtClause c d
            genEqClause :: Name -> (Name,[Type]) -> ClauseQ
            genEqClause conArg (constr, args) = do 
              varXs <- newNames (length args) "x"
              varYs <- newNames (length args) "y"
              let patX = ConP constr $ map VarP varXs
              let patY = ConP constr $ map VarP varYs
              body <- eqDBody conArg (zip3 varXs varYs args)
              return $ Clause [patX, patY] (NormalB body) []
            eqDBody :: Name -> [(Name, Name, Type)] -> ExpQ
            eqDBody conArg x =
                [|liftM compList (sequence $(listE $ map (eqDB conArg) x))|]
            eqDB :: Name -> (Name, Name, Type) -> ExpQ
            eqDB conArg (x, y, tp)
                | containsType tp (VarT conArg) =
                    [| compareD $(varE x) $(varE y) |]
                | otherwise =
                    [|pcompare $(varE x) $(varE y) |]
            genLtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return LT |]) []
            genGtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return GT |]) []