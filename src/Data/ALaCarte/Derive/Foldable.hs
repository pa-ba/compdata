{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.Foldable
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Derive.Foldable
    ( instanceFoldable
    )where

import Data.ALaCarte.Derive.Utils
import Language.Haskell.TH
import Data.Foldable
import Data.Monoid
import Data.Maybe
import qualified Prelude as P (foldl,foldr,foldl1,foldr1)
import Prelude hiding  (foldl,foldr,foldl1,foldr1)


instanceFoldable :: Name -> Q [Dec]
instanceFoldable fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''Foldable) complType
  constrs' <- mapM (mkPatAndVars . isFarg fArg . normalCon') constrs
  foldDecl <- funD 'fold (map foldClause constrs')
  foldMapDecl <- funD 'foldMap (map foldMapClause constrs')
  foldlDecl <- funD 'foldl (map foldlClause constrs')
  foldrDecl <- funD 'foldr (map foldrClause constrs')
  foldl1Decl <- funD 'foldl1 (map foldl1Clause constrs')
  foldr1Decl <- funD 'foldr1 (map foldr1Clause constrs')
  return $ [InstanceD [] classType [foldDecl,foldMapDecl,foldlDecl,foldrDecl,foldl1Decl,foldr1Decl]]
      where isFarg fArg (constr, args) = (constr, map (== fArg) args)
            filterVar incl x
                | incl = Just $ varE x
                | otherwise = Nothing
            filterVars args varNs = catMaybes $ zipWith filterVar args varNs
            mkCPat constr args varNs = ConP constr $ zipWith mkPat args varNs
            mkPat True x = VarP x
            mkPat False _ = WildP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (mkCPat constr args varNs, filterVars args varNs)
            foldClause (pat,vars) =
                do body <- if null vars
                           then [|mempty|]
                           else P.foldl1 (\ x y -> [|$x `mappend` $y|]) vars
                   return $ Clause [pat] (NormalB body) []
            foldMapClause (pat,vars) =
                do fn <- newName "y"
                   let f = varE fn
                       fp = if null vars then WildP else VarP fn
                   body <- case vars of
                             [] -> [|mempty|]
                             (z:r) -> P.foldl (\ x y -> [|$x `mappend` $f $y|]) [|$f $z|] r
                   return $ Clause [fp, pat] (NormalB body) []
            foldlClause (pat,vars) =
                do fn <- newName "f"
                   en <- newName "e"
                   let f = varE fn
                       e = varE en
                       fp = if null vars then WildP else VarP fn
                       ep = VarP en
                   body <- P.foldl (\ x y -> [|$f $x $y|]) e vars
                   return $ Clause [fp, ep, pat] (NormalB body) []
            foldrClause (pat,vars) =
                do fn <- newName "f"
                   en <- newName "e"
                   let f = varE fn
                       e = varE en
                       fp = if null vars then WildP else VarP fn
                       ep = VarP en
                   body <- P.foldr (\ x y -> [|$f $x $y|]) e vars
                   return $ Clause [fp, ep, pat] (NormalB body) []
            foldl1Clause (pat,vars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = case vars of
                              (_:_:_) -> VarP fn
                              _ -> WildP 
                   body <- case vars of 
                             [] -> [|undefined|] 
                             _ -> P.foldl1 (\ x y -> [|$f $x $y|]) vars
                   return $ Clause [fp, pat] (NormalB body) []
            foldr1Clause (pat,vars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = case vars of
                              (_:_:_) -> VarP fn
                              _ -> WildP 
                   body <- case vars of 
                             [] -> [|undefined|] 
                             _ -> P.foldr1 (\ x y -> [|$f $x $y|]) vars
                   return $ Clause [fp, pat] (NormalB body) []