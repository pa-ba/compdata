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
import Data.Traversable
import Data.Foldable hiding (or)
import Control.Applicative
import Control.Monad hiding (mapM, sequence)
import qualified Prelude as P (foldl, mapM)
import Prelude hiding  (foldl,mapM, sequence)

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
                | incl = farg $ varE x
                | otherwise = nonFarg $ varE x
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat x = VarP x
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs, filterVars args varNs, or args)
            traverseClause (con, pat,vars',hasFargs) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       vars = vars' (\x -> [|$f $x|]) (\x -> [|pure $x|])
                   body <- P.foldl (\ x y -> [|$x <*> $y|]) [|pure $con|] vars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceAClause (con, pat,vars',hasFargs) =
                do 
                   let vars = vars' id (\x -> [|pure $x|])
                   body <- P.foldl (\ x y -> [|$x <*> $y|]) [|pure $con|] vars
                   return $ Clause [pat] (NormalB body) []
            mapMClause (con, pat,vars',hasFargs) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = if hasFargs then VarP fn else WildP
                       vars = vars' (\x -> [|$f $x|]) (\x -> [|return $x|])
                   body <- P.foldl (\ x y -> [|$x `ap` $y|]) [|return $con|] vars
                   return $ Clause [fp, pat] (NormalB body) []
            sequenceClause (con, pat,vars',hasFargs) =
                do 
                   let vars = vars' id (\x -> [|return $x|])
                   body <- P.foldl (\ x y -> [|$x `ap` $y|]) [|return $con|] vars
                   return $ Clause [pat] (NormalB body) []
