{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.Functor
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
  kind taking at least two arguments. -}
instanceHDifunctor :: Name -> Q [Dec]
instanceHDifunctor fname = do
  -- Comments below apply to the example where name = T, args = [a,b,c], and
  -- constrs = [(X,[c]), (Y,[a,c]), (Z,[b -> c])], i.e. the data type
  -- declaration: T a b c = X c | Y a c | Z (b -> c)
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- coArg = c (covariant difunctor argument)
  let coArg :: Name = tyVarBndrName $ last args'
  -- conArg = b (contravariant difunctor argument)
  let conArg :: Name = tyVarBndrName $ last $ init args'
  -- argNames = [a]
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  -- compType = T a
  let complType = foldl AppT (ConT name) argNames
  -- classType = HDifunctor (T a)
  let classType = AppT (ConT ''HDifunctor) complType
  -- constrs' = [(X,[c]), (Y,[a,c]), (Z,[b -> c])]
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  dimapDecl <- funD 'dimap (map (dimapClause conArg coArg) constrs')
  return [InstanceD [] classType [dimapDecl]]
      where dimapClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            dimapClause conArg coArg (constr, args) = do
              fn <- newName "_f"
              gn <- newName "_g"
              varNs <- newNames (length args) "x"
              let f = varE fn
              let g = varE gn
              let fp = VarP fn
              let gp = VarP gn
              -- Pattern for the constructor
              let pat = ConP constr $ map VarP varNs
              body <- dimapArgs conArg coArg f g (zip varNs args) (conE constr)
              return $ Clause [fp, gp, pat] (NormalB body) []
            dimapArgs :: Name -> Name -> ExpQ -> ExpQ
                      -> [(Name, Type)] -> ExpQ -> ExpQ
            dimapArgs _ _ _ _ [] acc =
                acc
            dimapArgs conArg coArg f g ((x,tp):tps) acc =
                dimapArgs conArg coArg f g tps
                          (acc `appE` (dimapArg conArg coArg tp f g `appE` varE x))
            -- Given the name of the difunctor variables, a type, and the two
            -- arguments to dimap, return the expression that should be applied
            -- to the parameter of the given type.
            -- Example: dimapArg a b (a -> b) f g yields the expression
            -- [|\x -> g . x . f|]
            dimapArg :: Name -> Name -> Type -> ExpQ -> ExpQ -> ExpQ
            dimapArg conArg coArg tp f g =
                -- No need to descend into tp if it does not contain the
                -- difunctor type variables
                if not (containsType tp (VarT conArg) ||
                        containsType tp (VarT coArg)) then
                    [|id|]
                else
                    case tp of
                      ConT _ ->
                          [|id|]
                      AppT (VarT a) _
                          | a == conArg -> f
                          | a == coArg -> g
                      AppT (AppT ArrowT tp1) tp2 -> do
                          xn <- newName "x"
                          let ftp1 = dimapArg conArg coArg tp1 f g
                          let ftp2 = dimapArg conArg coArg tp2 f g
                          lamE [varP xn]
                               (infixE (Just ftp2)
                                       [|(.)|]
                                       (Just $ infixE (Just $ varE xn)
                                                      [|(.)|]
                                                      (Just ftp1)))
                      AppT _ tp' ->
                          [|fmap|] `appE` dimapArg conArg coArg tp' f g
                      SigT tp' _ ->
                          dimapArg conArg coArg tp' f g
                      _ ->
                          error $ "unsopported type: " ++ show tp