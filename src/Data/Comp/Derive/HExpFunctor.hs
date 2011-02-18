{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.HExpFunctor
-- Copyright   :  (c) 2011 Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HExpFunctor@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.HExpFunctor
    (
     HExpFunctor,
     instanceHExpFunctor
    ) where

import Data.Comp.Multi.HExpFunctor
import Data.Comp.Derive.Utils
import Language.Haskell.TH

{-| Derive an instance of 'HExpFunctor' for a type constructor of any 
 higher-order kind taking at least two arguments. -}
instanceHExpFunctor :: Name -> Q [Dec]
instanceHExpFunctor fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  let fArg :: Name = tyVarBndrName $ last args'
  let argNames = map (VarT . tyVarBndrName) (init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''HExpFunctor) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  hxmapDecl <- funD 'hxmap (map (hxmapClause fArg) constrs')
  return [InstanceD [] classType [hxmapDecl]]
      where hxmapClause :: Name -> (Name,[Type]) -> ClauseQ
            hxmapClause fArg (constr, args) = do
              fn <- newName "_f"
              gn <- newName "_g"
              varNs <- newNames (length args) "x"
              let f = varE fn
              let g = varE gn
              let fp = VarP fn
              let gp = VarP gn
              -- Pattern for the constructor
              let pat = ConP constr $ map VarP varNs
              body <- hxmapArgs fArg f g (zip varNs args) (conE constr)
              return $ Clause [fp, gp, pat] (NormalB body) []
            hxmapArgs :: Name -> ExpQ -> ExpQ -> [(Name, Type)] -> ExpQ -> ExpQ
            hxmapArgs _ _ _ [] acc =
                acc
            hxmapArgs fArg f g ((x,tp):tps) acc =
                hxmapArgs fArg f g tps (acc `appE`
                                       (hxmapArg fArg tp f g `appE` varE x))
            -- Given the name of the functor variable, a type, and the two
            -- arguments to xmap, return the expression that should be applied
            -- to the parameter of the given type.
            -- Example: xmapArg b (b -> b) f g yields the expression
            -- [|\x -> f . x . g|]
            hxmapArg :: Name -> Type -> ExpQ -> ExpQ -> ExpQ
            hxmapArg fArg tp f g =
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
                              hxmapArg fArg tp' f g
                      VarT a ->
                          -- Apply f if we have reached the functor variable
                          if a == fArg then f else [|id|]
                      ConT _ ->
                          [|id|]
                      AppT (AppT ArrowT tp1) tp2 -> do
                          -- Note that f and g are swapped in the contravariant
                          -- type tp1
                          xn <- newName "x"
                          let ftp1 = hxmapArg fArg tp1 g f
                          let ftp2 = hxmapArg fArg tp2 f g
                          lamE [varP xn]
                               (infixE (Just ftp2)
                                       [|(.)|]
                                       (Just $ infixE (Just $ varE xn)
                                                      [|(.)|]
                                                      (Just ftp1)))
                      AppT _ tp' ->
                          [|fmap|] `appE` hxmapArg fArg tp' f g
                      SigT tp' _ ->
                          hxmapArg fArg tp' f g
                      _ ->
                          error $ "unsopported type: " ++ show tp