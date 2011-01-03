{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.Traversable
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Derive.Traversable
    ( instanceTraversable
    )where

import Data.ALaCarte.Derive.Utils
import Language.Haskell.TH
import Data.Maybe
import Data.Traversable
import Data.Foldable hiding (or)
import Control.Applicative
import Control.Monad hiding (mapM, sequence)
import qualified Prelude as P (foldl, foldr, mapM)
import Prelude hiding  (foldl, foldr,mapM, sequence)

instanceTraversable :: Name -> Q [Dec]
instanceTraversable fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''Traversable) complType
  constrs' <- P.mapM (mkPatAndVars . isFarg fArg . normalCon') constrs
  traverseDecl <- funD 'traverse (map traverseClause constrs')
  sequenceADecl <- funD 'sequenceA (map sequenceAClause constrs')
  mapMDecl <- funD 'mapM (map mapMClause constrs')
  sequenceDecl <- funD 'sequence (map sequenceClause constrs')
  return $ [InstanceD [] classType [traverseDecl, sequenceADecl,mapMDecl, sequenceDecl]]
      where isFarg fArg (constr, args) = (constr, map (== fArg) args)
            filterVar farg nonFarg incl x
                | incl = farg x
                | otherwise = nonFarg x
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat x = VarP x
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           (\ f g -> filterVars args varNs (f . varE) (g . varE)),
                           or args, map varE varNs, catMaybes $ filterVars args varNs Just (const Nothing))
            traverseClause (con, pat,vars',hasFargs,_,_) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       vars = vars' (\x -> [|$f $x|]) (\x -> [|pure $x|])
                   body <- P.foldl (\ x y -> [|$x <*> $y|]) [|pure $con|] vars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceAClause (con, pat,vars',hasFargs,_,_) =
                do let vars = vars' id (\x -> [|pure $x|])
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
                   body <- P.foldr (\ x y -> [|$f $(varE x)  >>= $(lamE [varP x] y)|])
                           [|return $conAp|] fvars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceClause (con, pat,_,hasFargs,allVars, fvars) =
                do let conAp = P.foldl appE con allVars
                   body <- P.foldr (\ x y -> [|$(varE x)  >>= $(lamE [varP x] y)|])
                           [|return $conAp|] fvars
                   return $ Clause [pat] (NormalB body) []
