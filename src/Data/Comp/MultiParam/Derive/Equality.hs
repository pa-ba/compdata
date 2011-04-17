{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.Equality
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @EqHD@.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam.Derive.Equality
    (
     EqHD(..),
     instanceEqHD
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.MultiParam.HDifunctor (K(..))
import Data.Comp.MultiParam.Equality
import Control.Monad
import Language.Haskell.TH hiding (Cxt, match)

{-| Derive an instance of 'EqHD' for a type constructor of any parametric
  kind taking at least two arguments. -}
instanceEqHD :: Name -> Q [Dec]
instanceEqHD fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Name = tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Name = tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''EqHD) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  let defC = if length constrs < 2 then
                 []
             else
                 [clause [wildP,wildP] (normalB [|return False|]) []]
  eqHDDecl <- funD 'eqHD (map (eqHDClause coArg conArg) constrs' ++ defC)
  return [InstanceD [] classType [eqHDDecl]]
      where eqHDClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            eqHDClause coArg conArg (constr, args) = do
              varXs <- newNames (length args) "x"
              varYs <- newNames (length args) "y"
              -- Patterns for the constructors
              let patx = ConP constr $ map VarP varXs
              let paty = ConP constr $ map VarP varYs
              body <- eqHDBody coArg conArg (zip3 varXs varYs args)
              return $ Clause [patx,paty] (NormalB body) []
            eqHDBody :: Name -> Name -> [(Name, Name, Type)] -> ExpQ
            eqHDBody coArg conArg x =
                [|liftM and (sequence $(listE $ map (eqHDB coArg conArg) x))|]
            eqHDB :: Name -> Name -> (Name, Name, Type) -> ExpQ
            eqHDB coArg conArg (x, y, tp)
                | containsType tp (VarT conArg) ||
                  not (containsType tp (VarT coArg)) = [| peq (K $(varE x)) (K $(varE y)) |]
                | otherwise = [| peq $(varE x) $(varE y) |]