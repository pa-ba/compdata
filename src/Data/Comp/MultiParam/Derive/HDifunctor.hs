{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.HDifunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HDifunctor@.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Derive.HDifunctor
    (
     HDifunctor,
     instanceHDifunctor
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.MultiParam.HDifunctor
import Language.Haskell.TH

{-| Derive an instance of 'HDifunctor' for a type constructor of any parametric
  kind taking at least three arguments. -}
instanceHDifunctor :: Name -> Q [Dec]
instanceHDifunctor fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Name = tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Name = tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''HDifunctor) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  hdimapDecl <- funD 'hdimap (map (hdimapClause coArg conArg) constrs')
  return [InstanceD [] classType [hdimapDecl]]
      where hdimapClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            hdimapClause coArg conArg (constr, args) = do
              fn <- newName "_f"
              gn <- newName "_g"
              varNs <- newNames (length args) "x"
              let f = varE fn
              let g = varE gn
              let fp = VarP fn
              let gp = VarP gn
              -- Pattern for the constructor
              let pat = ConP constr $ map VarP varNs
              body <- hdimapArgs coArg conArg f g (zip varNs args) (conE constr)
              return $ Clause [fp, gp, pat] (NormalB body) []
            hdimapArgs :: Name -> Name -> ExpQ -> ExpQ
                      -> [(Name, Type)] -> ExpQ -> ExpQ
            hdimapArgs _ _ _ _ [] acc =
                acc
            hdimapArgs coArg conArg f g ((x,tp):tps) acc =
                hdimapArgs coArg conArg f g tps
                          (acc `appE` (hdimapArg coArg conArg tp f g `appE` varE x))
            hdimapArg :: Name -> Name -> Type -> ExpQ -> ExpQ -> ExpQ
            hdimapArg coArg conArg tp f g
                | containsType tp (VarT conArg) = [| hdimap $f $g |]
                | not (containsType tp (VarT coArg)) = [| id |]
                | otherwise =
                    case tp of
                      ConT _ ->
                          [|id|]
                      AppT (VarT a) _
                          | a == coArg -> g
                      AppT _ tp' ->
                          [|fmap|] `appE` hdimapArg conArg coArg tp' f g
                      SigT tp' _ ->
                          hdimapArg conArg coArg tp' f g
                      _ ->
                          error $ "unsopported type: " ++ show tp