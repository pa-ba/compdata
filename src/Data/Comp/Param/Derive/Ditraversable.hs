{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.Ditraversable
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @Ditraversable@.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive.Ditraversable
    (
     Ditraversable,
     instanceDitraversable
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Param.Ditraversable
import Data.Traversable (mapM)
import Language.Haskell.TH
import Data.Maybe
import Control.Monad hiding (mapM)
import Prelude hiding (mapM)

iter 0 _ e = e
iter n f e = iter (n-1) f (f `appE` e)

iter' n f e = run n f e
    where run 0 _ e = e
          run m f e = let f' = iter (m-1) [|fmap|] f
                        in run (m-1) f (f' `appE` e)

{-| Derive an instance of 'Traversable' for a type constructor of any
  first-order kind taking at least one argument. -}
instanceDitraversable :: Name -> Q [Dec]
instanceDitraversable fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  monadType <- varT =<< newName "m"
  domainType <- varT =<< newName "d"
  let fArg = VarT . tyVarBndrName $ last args
      aArg = VarT . tyVarBndrName $ last (init args)
      argNames = (map (VarT . tyVarBndrName) (init $ init args))
      complType = foldl AppT (ConT name) argNames
      classType = foldl1 AppT [ConT ''Ditraversable, complType, monadType,domainType]
      context   = [ClassP ''Monad [monadType]]
  normConstrs <- mapM normalConExp constrs
  mapM_ (checksAarg aArg) normConstrs
  constrs' <- mapM (mkPatAndVars . isFarg fArg) normConstrs
  mapMDecl <- funD 'dimapM (map mapMClause constrs')
  sequenceDecl <- funD 'disequence (map sequenceClause constrs')
  return [InstanceD context classType [mapMDecl,sequenceDecl]]
      where isFarg fArg (constr, args) = (constr, map (`containsType'` fArg) args)
            checksAarg aArg (_,args) = when (any (`containsType` aArg) args) $
                                       fail $ "Ditraversable instance cannot be derived if contravariant type variable a is used; please provide a custom instance for " ++ show fname
            filterVar _ nonFarg [] x  = nonFarg x
            filterVar farg _ [depth] x = farg depth x
            filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat = VarP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           \f g -> filterVars args varNs (\ d x -> f d (varE x)) (g . varE),
                           any (not . null) args, map varE varNs, catMaybes $ filterVars args varNs (curry Just) (const Nothing))

            -- Note: the monadic versions are not defined
            -- applicatively, as this results in a considerable
            -- performance penalty (by factor 2)!
            mapMClause (con, pat,_,hasFargs,allVars, fvars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       conAp = foldl appE con allVars
                       conBind (d,x) y = [| $(iter d [|mapM|] f) $(varE x)  >>= $(lamE [varP x] y)|]
                   body <- foldr conBind [|return $conAp|] fvars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceClause (con, pat,_,hasFargs,allVars, fvars) =
                do let conAp = foldl appE con allVars
                       conBind (d, x) y = [| $(iter' d [|sequence|] (varE x))  >>= $(lamE [varP x] y)|]
                   body <- foldr conBind [|return $conAp|] fvars
                   return $ Clause [pat] (NormalB body) []