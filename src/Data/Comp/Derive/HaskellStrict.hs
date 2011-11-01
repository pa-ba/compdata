{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.HaskellStrict
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HaskellStrict@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.HaskellStrict
    (
     makeHaskellStrict
     , haskellStrict
     , haskellStrict'
    ) where

import Data.Comp.Derive.Utils
import Language.Haskell.TH
import Data.Maybe
import Data.Comp.Thunk
import Data.Comp.Sum
import Data.Traversable
import Data.Foldable hiding (any,or)
import Control.Monad hiding (mapM, sequence)
import qualified Prelude as P (foldl, foldr, mapM, all)
import Prelude hiding  (foldl, foldr,mapM, sequence)


class HaskellStrict f where
    thunkSequence :: (Monad m) => f (TermT m g) -> m (f (TermT m g))
    thunkSequenceInject :: (Monad m, f :<: g) => f (TermT m g) -> TermT m g
    thunkSequenceInject t = thunk $ liftM inject $ thunkSequence t
    thunkSequenceInject' :: (Monad m, f :<: g) => f (TermT m g) -> TermT m g
    thunkSequenceInject' = thunkSequenceInject

haskellStrict :: (Monad m, HaskellStrict f, f :<: g) => f (TermT m g) -> TermT m g
haskellStrict = thunkSequenceInject

haskellStrict' :: (Monad m, HaskellStrict f, f :<: g) => f (TermT m g) -> TermT m g
haskellStrict' = thunkSequenceInject'

deepThunk d = iter d [|thunkSequence|]
    where iter 0 _ = [|whnf'|]
          iter 1 e = e
          iter n e = iter (n-1) ([|mapM|] `appE` e)

{-| Derive an instance of 'Traversable' for a type constructor of any
  first-order kind taking at least one argument. -}
makeHaskellStrict :: Name -> Q [Dec]
makeHaskellStrict fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = map (VarT . tyVarBndrName) (init args)
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''HaskellStrict) complType
  constrs_ <- P.mapM (liftM (isFarg fArg) . normalConStrExp) constrs
  if foldr (\ y x -> x && P.all null (snd y)) True constrs_
   then do
     sequenceDecl <- valD (varP 'thunkSequence) (normalB [|return|]) []
     injectDecl <- valD (varP 'thunkSequenceInject) (normalB [|inject|]) []
     injectDecl' <- valD (varP 'thunkSequenceInject') (normalB [|inject|]) []
     return [InstanceD [] classType [sequenceDecl, injectDecl, injectDecl']]
   else do
     constrs' <- P.mapM mkPatAndVars constrs_
     sequenceDecl <- funD 'thunkSequence (map sequenceClause' constrs')
     xn <- newName "x"
     injectDecl <- funD 'thunkSequenceInject [clause [varP xn] (normalB ([|thunk|] `appE` caseE (varE xn) (map injectMatch constrs'))) []] 
     injectDecl' <- funD 'thunkSequenceInject' (map injectClause' constrs')
     return [InstanceD [] classType [sequenceDecl, injectDecl, injectDecl']]
      where isFarg fArg (constr, args) = (constr, map (containsStr fArg) args)
            containsStr _ (NotStrict,_) = []
            containsStr fArg (IsStrict,ty) = ty `containsType'` fArg
            filterVar _ nonFarg [] x  = nonFarg x
            filterVar farg _ [depth] x = farg depth x
            filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat = VarP
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (conE constr, mkCPat constr varNs,
                           any (not . null) args, map varE varNs, catMaybes $ filterVars args varNs (curry Just) (const Nothing))
            sequenceClause' (con, pat,hasFargs,allVars, fvars) =
                do let conAp = P.foldl appE con allVars
                       conBind (d, x) y = [| $(deepThunk d `appE` (varE x))  >>= $(lamE [varP x] y)|]
                   body <- P.foldr conBind [|return $conAp|] fvars
                   return $ Clause [pat] (NormalB body) []
            injectMatch (con, pat,hasFargs,allVars, fvars) =
                do let conAp = P.foldl appE con allVars
                       conBind (d, x) y = [| $(deepThunk d `appE` (varE x))  >>= $(lamE [varP x] y)|]
                   body <- case fvars of
                             [] -> [|return (inject $conAp)|]
                             _ -> P.foldr conBind [|return (inject $conAp)|] fvars
                   return $ Match pat (NormalB body) []
            injectClause' (con, pat,hasFargs,allVars, fvars) =
                do let conAp = P.foldl appE con allVars
                       conBind (d, x) y = [| $(deepThunk d `appE` (varE x))  >>= $(lamE [varP x] y)|]
                   body <- case fvars of
                             [] -> [|inject $conAp|]
                             _ -> [| thunk |] `appE` P.foldr conBind [|return (inject $conAp)|] fvars
                   return $ Clause [pat] (NormalB body) []


-- {-| Derive an instance of 'Traversable' for a type constructor of any
--   first-order kind taking at least one argument. -}
-- makeHaskellStrict :: Name -> Q [Dec]
-- makeHaskellStrict fname = do
--   TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
--   let fArg = VarT . tyVarBndrName $ last args
--       argNames = map (VarT . tyVarBndrName) (init args)
--       complType = foldl AppT (ConT name) argNames
--       classType = AppT (ConT ''HaskellStrict) complType
--   constrs_ <- P.mapM (liftM (isFarg fArg) . normalConStrExp) constrs
--   if foldr (\ y x -> x && P.all null (snd y)) True constrs_
--    then do
--      sequenceDecl' <- valD (varP 'thunkSequence') (normalB [|return|]) []
--      sequenceDecl <- valD (varP 'thunkSequence) (normalB [|inject|]) []
--      return [InstanceD [] classType [sequenceDecl', sequenceDecl]]
--    else do
--      constrs' <- P.mapM mkPatAndVars constrs_
--      sequenceDecl' <- funD 'thunkSequence' (map sequenceClause' constrs')
--      sequenceDecl <- funD 'thunkSequence (map sequenceClause constrs')
--      return [InstanceD [] classType [sequenceDecl', sequenceDecl]]
--       where isFarg fArg (constr, args) = (constr, map (containsStr fArg) args)
--             containsStr _ (NotStrict,_) = []
--             containsStr fArg (IsStrict,ty) = ty `containsType'` fArg
--             filterVar _ nonFarg [] x  = nonFarg x
--             filterVar farg _ [depth] x = farg depth x
--             filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
--             filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
--             mkCPat constr varNs = ConP constr $ map mkPat varNs
--             mkPat = VarP
--             mkPatAndVars (constr, args) =
--                 do varNs <- newNames (length args) "x"
--                    return (conE constr, mkCPat constr varNs,
--                            any (not . null) args, map varE varNs, catMaybes $ filterVars args varNs (curry Just) (const Nothing))
--             sequenceClause' (con, pat,hasFargs,allVars, fvars) =
--                 do let conAp = P.foldl appE con allVars
--                        conBind (d, x) y = [| $(deepThunk d `appE` (varE x))  >>= $(lamE [varP x] y)|]
--                    body <- P.foldr conBind [|return $conAp|] fvars
--                    return $ Clause [pat] (NormalB body) []
