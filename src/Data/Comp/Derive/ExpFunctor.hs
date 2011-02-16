{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.ExpFunctor
-- Copyright   :  (c) 2011 Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @ExpFunctor@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.ExpFunctor
    ( ExpFunctor,
      instanceExpFunctor
    ) where

import Data.Comp.ExpFunctor
import Data.Comp.Derive.Utils
import Language.Haskell.TH

instanceExpFunctor :: Name -> Q [Dec]
instanceExpFunctor fname = do
  -- Comments below apply to the example where name = T, args = [a,b], and
  -- constrs = [(X,[a]), (Y,[a,b]), (Z,[b -> b])], i.e. the data type
  -- declaration: T a b = X a | Y a b | Z (b -> b)
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  -- fArg = b
  let fArg :: Name = tyVarBndrName $ last args
  -- argNames = [a]
  let argNames = map (VarT . tyVarBndrName) (init args)
  -- compType = T a
  let complType = foldl AppT (ConT name) argNames
  -- classType = ExpFunctor (T a)
  let classType = AppT (ConT ''ExpFunctor) complType
  -- constrs' = [(X,[a]), (Y,[a,b]), (Z,[b -> b])]
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  xmapDecl <- funD 'xmap (map (xmapClause fArg) constrs')
  return [InstanceD [] classType [xmapDecl]]
      where xmapClause :: Name -> (Name,[Type]) -> ClauseQ
            xmapClause fArg (constr, args) = do
              fn <- newName "_f"
              gn <- newName "_g"
              varNs <- newNames (length args) "x"
              let f = varE fn
              let g = varE gn
              let fp = VarP fn
              let gp = VarP gn
              -- Pattern for the constructor
              let pat = ConP constr $ map VarP varNs
              body <- xmapArgs fArg f g (zip varNs args) (conE constr)
              return $ Clause [fp, gp, pat] (NormalB body) []
            xmapArgs :: Name -> ExpQ -> ExpQ -> [(Name, Type)] -> ExpQ -> ExpQ
            xmapArgs _ _ _ [] acc =
                acc
            xmapArgs fArg f g ((x,tp):tps) acc =
                xmapArgs fArg f g tps (acc `appE`
                                       (xmapArg fArg tp f g `appE` varE x))
            -- Given the name of the functor variable, a type, and the two
            -- arguments to xmap, return the expression that should be applied
            -- to the parameter of the given type.
            -- Example: xmapArg b (b -> b) f g yields the expression
            -- [|\x -> f . x . g|]
            xmapArg :: Name -> Type -> ExpQ -> ExpQ -> ExpQ
            xmapArg fArg tp f g =
                -- No need to descend into tp if it does not contain the functor
                -- type variable
                if not $ containsType tp (VarT fArg) then
                    [|id|]
                else
                    case tp of
                      ForallT vars _ tp' ->
                          -- Check if the functor variable has been rebound
                          if any ((==) fArg . tyVarBndrName) vars then
                              [|id|]
                          else
                              xmapArg fArg tp' f g
                      VarT a ->
                          -- Apply f if we have reached the functor variable
                          if a == fArg then f else [|id|]
                      ConT _ ->
                          [|id|]
                      TupleT _ ->
                          error "unexpected top-level TupleT"
                      ArrowT ->
                          error "unexpected top-level ArrowT"
                      ListT ->
                          error "unexpected top-level ListT"
                      AppT (AppT ArrowT tp1) tp2 -> do
                          -- Note that f and g are swapped in the contravariant
                          -- type tp1
                          xn <- newName "x"
                          let ftp1 = xmapArg fArg tp1 g f
                          let ftp2 = xmapArg fArg tp2 f g
                          lamE [varP xn]
                               (infixE (Just ftp2)
                                       [|(.)|]
                                       (Just $ infixE (Just $ varE xn)
                                                      [|(.)|]
                                                      (Just ftp1)))
                      AppT _ tp' ->
                          [|fmap|] `appE` xmapArg fArg tp' f g
                      SigT tp' _ ->
                          xmapArg fArg tp' f g