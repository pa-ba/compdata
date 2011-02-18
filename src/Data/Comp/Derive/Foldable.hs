{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Foldable
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @Foldable@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.Foldable
    (
     Foldable,
     instanceFoldable
    ) where

import Data.Comp.Derive.Utils
import Language.Haskell.TH
import Data.Foldable
import Control.Monad
import Data.Monoid
import Data.Maybe
import qualified Prelude as P (foldl,foldr,foldl1,foldr1)
import Prelude hiding  (foldl,foldr,foldl1,foldr1)


iter 0 _ e = e
iter n f e = iter (n-1) f (f `appE` e)

iter' n f e = run n f e
    where run 0 _ e = e
          run m f e = let f' = iter (m-1) [|fmap|] f
                        in run (m-1) f (f' `appE` e)

{-| Derive an instance of 'Foldable' for a type constructor of any first-order
  kind taking at least one argument. -}
instanceFoldable :: Name -> Q [Dec]
instanceFoldable fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = (map (VarT . tyVarBndrName) (init args))
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''Foldable) complType
  constrs' <- mapM (mkPatAndVars  . isFarg fArg <=< normalConExp) constrs
  foldDecl <- funD 'fold (map foldClause constrs')
  foldMapDecl <- funD 'foldMap (map foldMapClause constrs')
  foldlDecl <- funD 'foldl (map foldlClause constrs')
  foldrDecl <- funD 'foldr (map foldrClause constrs')
  foldl1Decl <- funD 'foldl1 (map foldl1Clause constrs')
  foldr1Decl <- funD 'foldr1 (map foldr1Clause constrs')
  return [InstanceD [] classType [foldDecl,foldMapDecl,foldlDecl,foldrDecl,foldl1Decl,foldr1Decl]]
      where isFarg fArg (constr, args) = (constr, map (`containsType'` fArg) args)
            filterVar [] _ = Nothing
            filterVar [d] x =Just (d, varE x)
            filterVar _ _ =  error "functor variable occurring twice in argument type"
            filterVars args varNs = catMaybes $ zipWith filterVar args varNs
            mkCPat constr args varNs = ConP constr $ zipWith mkPat args varNs
            mkPat [] _ = WildP
            mkPat _ x = VarP x
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (mkCPat constr args varNs, filterVars args varNs)
            foldClause (pat,vars) =
                do body <- if null vars
                           then [|mempty|]
                           else P.foldl1 (\ x y -> [|$x `mappend` $y|])
                                    $ map (\(d,x) -> iter' d [|fold|] x) vars
                   return $ Clause [pat] (NormalB body) []
            foldMapClause (pat,vars) =
                do fn <- newName "y"
                   let f = varE fn
                       f' 0 = f
                       f' n = iter (n-1) [|fmap|] [| foldMap $f |]
                       fp = if null vars then WildP else VarP fn
                   body <- case vars of
                             [] -> [|mempty|]
                             (_:_) -> P.foldl1 (\ x y -> [|$x `mappend` $y|]) $ 
                                      map (\ (d,z) -> iter' (max (d-1) 0) [|fold|] (f' d `appE` z)) vars
                   return $ Clause [fp, pat] (NormalB body) []
            foldlClause (pat,vars) =
                do fn <- newName "f"
                   en <- newName "e"
                   let f = varE fn
                       e = varE en
                       fp = if null vars then WildP else VarP fn
                       ep = VarP en
                       conApp x (0,y) = [|$f $x $y|]
                       conApp x (1,y) = [|foldl $f $x $y|]
                       conApp x (d,y) = let hidEndo = iter (d-1) [|fmap|] [|Endo . flip (foldl $f)|] `appE` y
                                            endo = iter' (d-1) [|fold|] hidEndo
                                        in [| appEndo $endo $x|]
                   body <- P.foldl conApp e vars
                   return $ Clause [fp, ep, pat] (NormalB body) []
            foldrClause (pat,vars) =
                do fn <- newName "f"
                   en <- newName "e"
                   let f = varE fn
                       e = varE en
                       fp = if null vars then WildP else VarP fn
                       ep = VarP en
                       conApp (0,x) y = [|$f $x $y|]
                       conApp (1,x) y = [|foldr $f $y $x |]
                       conApp (d,x) y = let hidEndo = iter (d-1) [|fmap|] [|Endo . flip (foldr $f)|] `appE` x
                                            endo = iter' (d-1) [|fold|] hidEndo
                                        in [| appEndo $endo $y|]
                   body <- P.foldr conApp e vars
                   return $ Clause [fp, ep, pat] (NormalB body) []
            foldl1Clause (pat,vars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = case vars of
                              (d,_):r
                                  | d > 0 || not (null r) -> VarP fn                              
                              _ -> WildP 
                       mkComp (d,x) = iter' d [|foldl1 $f|] x
                   body <- case vars of 
                             [] -> [|undefined|] 
                             _ -> P.foldl1 (\ x y -> [|$f $x $y|]) $ map mkComp vars
                   return $ Clause [fp, pat] (NormalB body) []
            foldr1Clause (pat,vars) =
                do fn <- newName "f"
                   let f = varE fn
                       fp = case vars of
                              (d,_):r
                                  | d > 0 || not (null r) -> VarP fn                              
                              _ -> WildP 
                       mkComp (d,x) = iter' d [|foldr1 $f|] x
                   body <- case vars of 
                             [] -> [|undefined|] 
                             _ -> P.foldr1 (\ x y -> [|$f $x $y|]) $ map mkComp vars
                   return $ Clause [fp, pat] (NormalB body) []