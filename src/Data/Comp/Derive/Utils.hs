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


import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad
import Language.Haskell.TH.ExpandSyns

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

 > $(derive [instanceFunctor, instanceShowF] [''Exp])
 -}
derive :: [Name -> Q [Dec]] -> [Name] -> Q [Dec]
derive ders names = liftM concat $ sequence [der name | der <- ders, name <- names]