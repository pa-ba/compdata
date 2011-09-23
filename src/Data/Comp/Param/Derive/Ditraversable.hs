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
     makeDitraversable
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
makeDitraversable :: Name -> Q [Dec]
makeDitraversable fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  monadType <- varT =<< newName "m"
  domainType <- varT =<< newName "d"
  let fArg = VarT . tyVarBndrName $ last args
      aArg = VarT . tyVarBndrName $ last (init args)
      funTy = foldl AppT ArrowT [aArg,fArg]
      argNames = map (VarT . tyVarBndrName) (init $ init args)
      complType = foldl AppT (ConT name) argNames
      classType = foldl1 AppT [ConT ''Ditraversable, complType, monadType,domainType]
  normConstrs <- mapM normalConExp constrs
  let hasFunTy = any (checksAarg funTy) normConstrs
      context = ClassP ''Monad [monadType] :
                [ClassP ''Ditraversable [ArrowT,monadType,domainType] | hasFunTy]
  constrs' <- mapM (mkPatAndVars . isFarg fArg funTy) normConstrs
  mapMDecl <- funD 'dimapM (map mapMClause constrs')
  sequenceDecl <- funD 'disequence (map sequenceClause constrs')
  return [InstanceD context classType [mapMDecl,sequenceDecl]]
      where isFarg fArg funTy (constr, args) =
                (constr, map (\t -> (t `containsType'` fArg, t `containsType'` funTy)) args)
            checksAarg aArg (_,args) = any (`containsType` aArg) args
            filterVar _ _ nonFarg ([],[]) x  = nonFarg x
            filterVar farg _ _ ([depth],[]) x = farg depth x
            filterVar _ aarg _ ([_],[depth]) x = aarg depth x
            filterVar _ _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg aarg nonFarg = zipWith (filterVar farg aarg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat = VarP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           any (not . null . fst) args || any (not . null . snd) args, map varE varNs,
                           catMaybes $ filterVars args varNs (\x y -> Just (False,x,y)) (\x y -> Just (True, x, y)) (const Nothing))

            -- Note: the monadic versions are not defined
            -- applicatively, as this results in a considerable
            -- performance penalty (by factor 2)!
            mapMClause (con, pat,hasFargs,allVars, fvars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       conAp = foldl appE con allVars
                       addDi False _ x = x
                       addDi True d x = [|dimapM $(f)|]
                       conBind (fun,d,x) y = [| $(iter d [|mapM|] (addDi fun d f)) $(varE x)  >>= $(lamE [varP x] y)|]
                   body <- foldr conBind [|return $conAp|] fvars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceClause (con, pat,hasFargs,allVars, fvars) =
                do let conAp = foldl appE con allVars
                       varE' False _ x = varE x
                       varE' True d x = appE (iter d [|fmap|] [|disequence|]) (varE x)
                       conBind (fun,d, x) y = [| $(iter' d [|sequence|] (varE' fun d x))  >>= $(lamE [varP x] y)|]
                   body <- foldr conBind [|return $conAp|] fvars
                   return $ Clause [pat] (NormalB body) []