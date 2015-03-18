{-# LANGUAGE CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Utils
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines some utility functions for deriving instances
-- for functor based type classes.
--
--------------------------------------------------------------------------------
module Data.Comp.Derive.Utils where


import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.ExpandSyns
import Language.Haskell.TH.Syntax

-- reportError is introduced only from version 7.6 of GHC
#if __GLASGOW_HASKELL__ < 706
reportError :: String -> Q ()
reportError = report True
#endif

{-|
  This is the @Q@-lifted version of 'abstractNewtypeQ.
-}
abstractNewtypeQ :: Q Info -> Q Info
abstractNewtypeQ = liftM abstractNewtype

{-|
  This function abstracts away @newtype@ declaration, it turns them into
  @data@ declarations.
-}
abstractNewtype :: Info -> Info
abstractNewtype (TyConI (NewtypeD cxt name args constr derive))
    = TyConI (DataD cxt name args [constr] derive)
abstractNewtype owise = owise

{-|
  This function provides the name and the arity of the given data constructor.
-}
normalCon :: Con -> (Name,[StrictType])
normalCon (NormalC constr args) = (constr, args)
normalCon (RecC constr args) = (constr, map (\(_,s,t) -> (s,t)) args)
normalCon (InfixC a constr b) = (constr, [a,b])
normalCon (ForallC _ _ constr) = normalCon constr


normalCon' :: Con -> (Name,[Type])
normalCon' = fmap (map snd) . normalCon

-- | Same as normalCon' but expands type synonyms.
normalConExp :: Con -> Q (Name,[Type])
normalConExp c = do
  let (n,ts) = normalCon' c
  ts' <- mapM expandSyns ts
  return (n, ts')


-- | Same as normalConExp' but retains strictness annotations.
normalConStrExp :: Con -> Q (Name,[StrictType])
normalConStrExp c = do
  let (n,ts) = normalCon c
  ts' <- mapM (\ (st,ty) -> do ty' <- expandSyns ty; return (st,ty')) ts
  return (n, ts')


{-|
  This function provides the name and the arity of the given data constructor.
-}
abstractConType :: Con -> (Name,Int)
abstractConType (NormalC constr args) = (constr, length args)
abstractConType (RecC constr args) = (constr, length args)
abstractConType (InfixC _ constr _) = (constr, 2)
abstractConType (ForallC _ _ constr) = abstractConType constr

{-|
  This function returns the name of a bound type variable
-}
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _) = n

containsType :: Type -> Type -> Bool
containsType s t
             | s == t = True
             | otherwise = case s of
                             ForallT _ _ s' -> containsType s' t
                             AppT s1 s2 -> containsType s1 t || containsType s2 t
                             SigT s' _ -> containsType s' t
                             _ -> False

containsType' :: Type -> Type -> [Int]
containsType' = run 0
    where run n s t
             | s == t = [n]
             | otherwise = case s of
                             ForallT _ _ s' -> run n s' t
                             -- only going through the right-hand side counts!
                             AppT s1 s2 -> run n s1 t ++ run (n+1) s2 t
                             SigT s' _ -> run n s' t
                             _ -> []


{-|
  This function provides a list (of the given length) of new names based
  on the given string.
-}
newNames :: Int -> String -> Q [Name]
newNames n name = replicateM n (newName name)

tupleTypes n m = map tupleTypeName [n..m]

{-| Helper function for generating a list of instances for a list of named
 signatures. For example, in order to derive instances 'Functor' and
 'ShowF' for a signature @Exp@, use derive as follows (requires Template
 Haskell):

 > $(derive [makeFunctor, makeShowF] [''Exp])
 -}
derive :: [Name -> Q [Dec]] -> [Name] -> Q [Dec]
derive ders names = liftM concat $ sequence [der name | der <- ders, name <- names]

-- | This function lifts type class instances over sums
-- ofsignatures. To this end it assumes that it contains only methods
-- with types of the form @f t1 .. tn -> t@ where @f@ is the signature
-- that is used to construct sums. Since this function is generic it
-- assumes as its first argument the name of the function that is
-- used to lift methods over sums i.e. a function of type
--
-- @
-- (f t1 .. tn -> t) -> (g t1 .. tn -> t) -> ((f :+: g) t1 .. tn -> t)
-- @
--
-- where @:+:@ is the sum type constructor. The second argument to
-- this function is expected to be the name of that constructor. The
-- last argument is the name of the class whose instances should be
-- lifted over sums.

liftSumGen :: Name -> Name -> Name -> Q [Dec]
liftSumGen caseName sumName fname = do
  ClassI (ClassD _ name targs_ _ decs) _ <- reify fname
  let targs = map tyVarBndrName targs_
  splitM <- findSig targs decs
  case splitM of
    Nothing -> do reportError $ "Class " ++ show name ++ " cannot be lifted to sums!"
                  return []
    Just (ts1_, ts2_) -> do
      let f = VarT $ mkName "f"
      let g = VarT $ mkName "g"
      let ts1 = map VarT ts1_
      let ts2 = map VarT ts2_
      let cxt = [foldl AppT (ConT name) (ts1 ++ f : ts2),
                 foldl AppT (ConT name) (ts1 ++ g : ts2)]
      let tp = ((ConT sumName `AppT` f) `AppT` g)
      let complType = foldl AppT (foldl AppT (ConT name) ts1 `AppT` tp) ts2
      decs' <- sequence $ concatMap decl decs
      return [InstanceD cxt complType decs']
        where decl :: Dec -> [DecQ]
              decl (SigD f _) = [funD f [clause f]]
              decl _ = []
              clause :: Name -> ClauseQ
              clause f = do x <- newName "x"
                            let b = NormalB (VarE caseName `AppE` VarE f `AppE` VarE f `AppE` VarE x)
                            return $ Clause [VarP x] b []


findSig :: [Name] -> [Dec] -> Q (Maybe ([Name],[Name]))
findSig targs decs = case map run decs of
                       []  -> return Nothing
                       mx:_ -> do x <- mx
                                  case x of
                                    Nothing -> return Nothing
                                    Just n -> return $ splitNames n targs
  where run :: Dec -> Q (Maybe Name)
        run (SigD _ ty) = do
          ty' <- expandSyns ty
          return $ getSig False ty'
        run _ = return Nothing
        getSig t (ForallT _ _ ty) = getSig t ty
        getSig False (AppT (AppT ArrowT ty) _) = getSig True ty
        getSig True (AppT ty _) = getSig True ty
        getSig True (VarT n) = Just n
        getSig _ _ = Nothing
        splitNames y (x:xs)
          | y == x = Just ([],xs)
          | otherwise = do (xs1,xs2) <- splitNames y xs
                           return (x:xs1,xs2)
        splitNames _ [] = Nothing
