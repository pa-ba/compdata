{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables, UndecidableInstances, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.Show
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @ShowHD@.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam.Derive.Show
    (
     PShow(..),
     ShowHD(..),
     instanceShowHD
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.MultiParam.FreshM
import Data.Comp.MultiParam.HDifunctor
import Control.Monad
import Language.Haskell.TH hiding (Cxt, match)

-- |Printing of parametric values.
class PShow a where
    pshow :: a i -> FreshM String

{-| Signature printing. An instance @ShowHD f@ gives rise to an instance
  @Show (Term f i)@. -}
class ShowHD f where
    showHD :: PShow a => f Var a i -> FreshM String

{-| Derive an instance of 'ShowHD' for a type constructor of any parametric
  kind taking at least three arguments. -}
instanceShowHD :: Name -> Q [Dec]
instanceShowHD fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Name = tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Name = tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''ShowHD) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  showHDDecl <- funD 'showHD (map (showHDClause coArg conArg) constrs')
  return [InstanceD [] classType [showHDDecl]]
      where showHDClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            showHDClause coArg conArg (constr, args) = do
              varXs <- newNames (length args) "x"
              -- Pattern for the constructor
              let patx = ConP constr $ map VarP varXs
              body <- showHDBody (nameBase constr) coArg conArg (zip varXs args)
              return $ Clause [patx] (NormalB body) []
            showHDBody :: String -> Name -> Name -> [(Name, Type)] -> ExpQ
            showHDBody constr coArg conArg x =
                [|liftM (unwords . (constr :) .
                         map (\x -> if elem ' ' x then "(" ++ x ++ ")" else x))
                        (sequence $(listE $ map (showHDB coArg conArg) x))|]
            showHDB :: Name -> Name -> (Name, Type) -> ExpQ
            showHDB coArg conArg (x, tp)
                | containsType tp (VarT conArg) = [| showHD $(varE x) |]
                | containsType tp (VarT coArg) = [| pshow $(varE x) |]
                | otherwise = [| return $ show $(varE x) |]