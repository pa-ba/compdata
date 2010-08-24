{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Arbitrary
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Arbitrary
    ( ArbitraryF,
      deriveArbitraryFs,
      deriveArbitraryF
    )where

import Test.QuickCheck
import Data.ALaCarte
import Data.ALaCarte.Derive
import Control.Applicative
import Control.Monad
import Language.Haskell.TH

{-|
  This class should be instantiated by functors @f@ such that @Term f@
  becomes an instance of 'Arbitrary'
-}

class ArbitraryF f where
    arbitraryF' :: Arbitrary v => [(Int,Gen (f v))]
    arbitraryF' = [(1,arbitraryF)]
    arbitraryF :: Arbitrary v => Gen (f v)
    arbitraryF = frequency arbitraryF'
    shrinkF :: Arbitrary v => f v -> [f v]
    shrinkF _ = []

{-| This lifts instances of 'ArbitraryF' to instances of 'Arbitrary'
for the corresponding term type. -}

instance (ArbitraryF f) => Arbitrary (Term f) where
    arbitrary = Term <$> arbitraryF
    shrink (Term expr) = map Term $ shrinkF expr

{-|
  This lifts instances of 'ArbitraryF' to instances of 'ArbitraryF' for 
  the corresponding context functor.
-}
instance (ArbitraryF f) => ArbitraryF (Context f) where
    arbitraryF = oneof [Term <$> arbitraryF , Hole <$> arbitrary]
    shrinkF (Term expr) = map Term $ shrinkF expr
    shrinkF (Hole a) = map Hole $ shrink a


{-| This lifts instances of 'ArbitraryF' to instances of 'Arbitrary'
for the corresponding context type.  -}

instance (ArbitraryF f, Arbitrary a) => Arbitrary (Context f a) where
    arbitrary = arbitraryF
    shrink = shrinkF


{-| Instances of 'ArbitraryF' are closed under forming sums.  -}

instance (ArbitraryF f , ArbitraryF g) => ArbitraryF (f :+: g) where
    arbitraryF' = map inl arbitraryF' ++ map inr arbitraryF'
        where inl (i,gen) = (i,Inl <$> gen)
              inr (i,gen) = (i,Inr <$> gen)
    shrinkF (Inl val) = map Inl (shrinkF val)
    shrinkF (Inr val) = map Inr (shrinkF val)

{-| This function derives instances for 'ArbitraryF' for list of data
types using 'deriveArbitraryF' -}

deriveArbitraryFs :: [Name] -> Q [Dec]
deriveArbitraryFs ns = liftM concat $ mapM deriveArbitraryF ns

{-| This template function generates an instance declaration of the
given data type name for the class 'ArbitraryF'. It is necessary that
all types that are used by the data type definition are themselves
instances of 'Arbitrary'.  -}

deriveArbitraryF :: Name -> Q [Dec]
deriveArbitraryF dt = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify dt
  let complType = foldl1 AppT (ConT name : map (VarT . tyVarBndrName) args)
      classType = AppT (ConT ''ArbitraryF) complType
  arbitraryDecl <- generateArbitraryFDecl constrs
  shrinkDecl <- generateShrinkFDecl constrs
  return $ [InstanceD [] classType [arbitraryDecl, shrinkDecl]]

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
    = do let constrsNum = length constrs
         genBody <- listE $ map (addNum constrsNum . constrGen . abstractConType) constrs
         let genClause = Clause [] (NormalB genBody) []
         return $ FunD genName [genClause]
    where addNum n e = [| (n,$e) |]
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
                   [| sized $ \ size ->
                        $(letE [valD 
                              newSizeP
                              (normalB [|((size - 1) `div` $constrsE ) `max` 0|])
                              [] ]
                          build) |]

{-|
  This function generates a declaration for the method 'shrink' using the given constructors.
  The constructors are supposed to belong to the same type.
-}
generateShrinkFDecl :: [Con] -> Q Dec
generateShrinkFDecl constrs
    = let clauses = map (generateClause.abstractConType) constrs
      in funD 'shrink clauses
  where generateClause (constr, n)
            = do varNs <- newNames n "x"
                 resVarNs <- newNames n "x'"
                 binds <- mapM (\(var,resVar) -> bindS (varP resVar) [| $(varE var) : shrink $(varE var) |]) $ zip varNs resVarNs
                 let ret = NoBindS $ AppE (VarE 'return) (foldl1 AppE ( ConE constr: map VarE resVarNs ))
                     stmtSeq = binds ++ [ret]
                     pat = ConP constr $ map VarP varNs
                 return $ Clause [pat] (NormalB $ AppE (VarE 'tail) (DoE stmtSeq)) []