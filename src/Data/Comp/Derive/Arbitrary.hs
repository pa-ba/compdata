{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Arbitrary
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @ArbitraryF@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.Arbitrary
    (
     ArbitraryF(..),
     makeArbitraryF,
     Arbitrary(..)
    )where

import Data.Comp.Derive.Utils hiding (derive)
import Language.Haskell.TH
import Test.QuickCheck
import qualified TemplateHaskell.Compat.V0208 as THCompat

{-| Signature arbitration. An instance @ArbitraryF f@ gives rise to an instance
  @Arbitrary (Term f)@. -}
class ArbitraryF f where
    arbitraryF' :: Arbitrary v => [(Int,Gen (f v))]
    arbitraryF' = [(1,arbitraryF)]
    arbitraryF :: Arbitrary v => Gen (f v)
    arbitraryF = frequency arbitraryF'
    shrinkF :: Arbitrary v => f v -> [f v]
    shrinkF _ = []

{-| Derive an instance of 'ArbitraryF' for a type constructor of any
  first-order kind taking at least one argument. It is necessary that
  all types that are used by the data type definition are themselves
  instances of 'Arbitrary'. -}
makeArbitraryF :: Name -> Q [Dec]
makeArbitraryF dt = do
  Just (DataInfo _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify dt
  let argNames = map (VarT . tyVarBndrName) (tail args)
      complType = foldl AppT (ConT name) argNames
      preCond = map (mkClassP ''Arbitrary . (: [])) argNames
      classType = AppT (ConT ''ArbitraryF) complType
  arbitraryDecl <- generateArbitraryFDecl constrs
  shrinkDecl <- generateShrinkFDecl constrs
  return [mkInstanceD preCond classType [arbitraryDecl, shrinkDecl]]

{-|
  This function generates a declaration of the method 'arbitrary' for the given
  list of constructors using 'generateGenDecl'.
-}
generateArbitraryFDecl :: [Con] -> Q Dec
generateArbitraryFDecl = generateGenDecl 'arbitraryF'

{-|
  This function generates a declaration of a generator having the given name using
  the given constructors, i.e., something like this:

  @
  \<name\> :: Gen \<type\>
  \<name\> = ...
  @

  where @\<type\>@ is the type of the given constructors. If the constructors do not belong
  to the same type this function fails. The generated function will generate only elements of
  this type using the given constructors. All argument types of these constructors are supposed
  to be instances of 'Arbitrary'.
-}

generateGenDecl :: Name -> [Con] -> Q Dec
generateGenDecl genName constrs
    = do genBody <- listE $ map (addNum . constrGen . abstractConType) constrs
         let genClause = Clause [] (NormalB genBody) []
         return $ FunD genName [genClause]
    where addNum e = [| (1,$e) |]
          constrGen :: (Name,Int) -> ExpQ
          constrGen (constr, n)
              = do varNs <- newNames n "x"
                   newSizeN <- newName "newSize"
                   let newSizeE = varE newSizeN
                   let newSizeP = varP newSizeN
                   let constrsE = litE . IntegerL . toInteger $ n
                   let binds = (`map` varNs) (\var -> bindS
                                                     (varP var)
                                                     [| resize $newSizeE arbitrary |] )
                   let apps =  appsE (conE constr: map varE varNs)
                   let build = doE $
                               binds ++
                               [noBindS [|return $apps|]]
                   if n == 0
                      then [|return $apps|]
                      else  [| sized $ \ size ->
                                 $(letE [valD
                                         newSizeP
                                         (normalB [|((size - 1) `div` $constrsE ) `max` 0|])
                                         [] ]
                                   build) |]

{-|
  This function generates a declaration for the method 'shrinkF' using the given constructors.
  The constructors are supposed to belong to the same type.
-}
generateShrinkFDecl :: [Con] -> Q Dec
generateShrinkFDecl constrs
    = let clauses = map (generateClause.abstractConType) constrs
      in funD 'shrinkF clauses
  where generateClause (constr, n)
            = do varNs <- newNames n "x"
                 resVarNs <- newNames n "x'"
                 binds <- mapM (\(var,resVar) -> bindS (varP resVar) [| $(varE var) : shrink $(varE var) |]) $ zip varNs resVarNs
                 let ret = NoBindS $ AppE (VarE 'return) (foldl1 AppE ( ConE constr: map VarE resVarNs ))
                     stmtSeq = binds ++ [ret]
                     pat = THCompat.conp constr $ map VarP varNs
                 return $ Clause [pat] (NormalB $ AppE (VarE 'tail) (THCompat.doE stmtSeq)) []
