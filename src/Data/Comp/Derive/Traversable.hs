{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Traversable
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @Traversable@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.Traversable
    (
     Traversable,
     makeTraversable
    ) where

import Control.Applicative
import Control.Monad hiding (mapM, sequence)
import Data.Comp.Derive.Utils
import Data.Comp.Derive.Compat
import Data.Foldable hiding (any, or)
import Data.Maybe
import Data.Traversable
import Language.Haskell.TH
import Prelude hiding (foldl, foldr, mapM, sequence)
import qualified Prelude as P (foldl, foldr, mapM)

iter 0 _ e = e
iter n f e = iter (n-1) f (f `appE` e)

iter' 0 _ e = e
iter' m f e = let f' = iter (m-1) [|fmap|] f
              in iter' (m-1) f (f' `appE` e)

{-| Derive an instance of 'Traversable' for a type constructor of any
  first-order kind taking at least one argument. -}
makeTraversable :: Name -> Q [Dec]
makeTraversable fname = do
  Just (DataInfo _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = map (VarT . tyVarBndrName) (init args)
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''Traversable) complType
  constrs' <- P.mapM (mkPatAndVars . isFarg fArg <=< normalConExp) constrs
  traverseDecl <- funD 'traverse (map traverseClause constrs')
  sequenceADecl <- funD 'sequenceA (map sequenceAClause constrs')
  mapMDecl <- funD 'mapM (map mapMClause constrs')
  sequenceDecl <- funD 'sequence (map sequenceClause constrs')
  return [mkInstanceD [] classType [traverseDecl, sequenceADecl, mapMDecl,sequenceDecl]]
      where isFarg fArg (constr, args, gadtTy) = (constr, map (`containsType'` getUnaryFArg fArg gadtTy) args)
            filterVar _ nonFarg [] x  = nonFarg x
            filterVar farg _ [depth] x = farg depth x
            filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = conP_ constr $ map mkPat varNs
            mkPat = VarP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           \f g -> filterVars args varNs (\ d x -> f d (varE x)) (g . varE),
                           any (not . null) args, map varE varNs, catMaybes $ filterVars args varNs (curry Just) (const Nothing))
            traverseClause (con, pat,vars',hasFargs,_allVars,_fVars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       vars = vars' (\d x -> iter d [|traverse|] f `appE` x) (\x -> [|pure $x|])
                   body <- P.foldl (\ x y -> [|$x <*> $y|]) [|pure $con|] vars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceAClause (con, pat,vars',_hasFargs,_,_) =
                do let vars = vars' (\d x -> iter' d [|sequenceA|] x) (\x -> [|pure $x|])
                   body <- P.foldl (\ x y -> [|$x <*> $y|]) [|pure $con|] vars
                   return $ Clause [pat] (NormalB body) []
            -- Note: the monadic versions are not defined
            -- applicatively, as this results in a considerable
            -- performance penalty (by factor 2)!
            mapMClause (con, pat,_,hasFargs,allVars, fvars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       conAp = P.foldl appE con allVars
                       conBind (d,x) y = [| $(iter d [|mapM|] f) $(varE x)  >>= $(lamE [varP x] y)|]
                   body <- P.foldr conBind [|return $conAp|] fvars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceClause (con, pat,_vars',_hasFargs,allVars, fvars) =
                do let conAp = P.foldl appE con allVars
                       conBind (d, x) y = [| $(iter' d [|sequence|] (varE x))  >>= $(lamE [varP x] y)|]
                   body <- P.foldr conBind [|return $conAp|] fvars
                   return $ Clause [pat] (NormalB body) []
