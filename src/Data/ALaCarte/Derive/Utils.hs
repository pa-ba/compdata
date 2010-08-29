--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Derive.Utils
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines some utility functions for deriving instances
-- for functor based type classes.
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Derive.Utils where


import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad
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


{-|
  This function provides a list (of the given length) of new names based
  on the given string.
-}
newNames :: Int -> String -> Q [Name]
newNames n name = replicateM n (newName name)

tupleTypes n m = map tupleTypeName [n..m]