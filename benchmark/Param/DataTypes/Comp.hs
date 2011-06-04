{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses,  FlexibleInstances,
  FlexibleContexts, UndecidableInstances, TypeOperators, ScopedTypeVariables,
  TypeSynonymInstances #-}

module Param.DataTypes.Comp 
    (
     module Param.DataTypes.Comp
    ) where

import Data.Comp.Param.Derive
import Data.Comp.Param.Show
import Data.Comp.Param
--import Data.Comp.Arbitrary ()
--import Data.Comp.Param.Show
--import Data.Traversable
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
--import Test.QuickCheck.Property

--import Control.Monad hiding (sequence_,mapM)
import Prelude hiding (sequence_,mapM)

-- base values

type ValueSig = Fun :+: Value
type ValueExpr = Term ValueSig
type ExprSig = Value :+: Op :+: Lam
type Expr = Term ExprSig
type SugarSig = Sugar :+: SugarLet :+: ExprSig
type SugarExpr = Term SugarSig
type BaseTypeSig = ValueT
type BaseType = Term BaseTypeSig

data ValueT a e = TInt
                | TBool
                | TPair e e
                | TFun e e

data Value a e = VInt Int
               | VBool Bool
               | VPair e e
data Fun a e = Fun (e -> e)

data Proj = ProjLeft | ProjRight
            deriving (Eq, Show)

data Op a e = Plus e e
            | Mult e e
            | If e e e
            | Eq e e
            | Lt e e
            | And e e
            | Not e
            | Proj Proj e

data Lam a e = Lam (a -> e)
             | App e e

data Sugar a e = Neg e
               | Minus e e
               | Gt e e
               | Or e e
               | Impl e e
data SugarLet a e = Let e (a -> e)

$(derive [makeDifunctor, makeFoldable, makeTraversable,
          makeEqD, makeShowD, smartConstructors]
         [''Value, ''Op, ''Sugar, ''ValueT])

$(derive [makeDifunctor, makeEqD, makeShowD, smartConstructors]
         [''Lam, ''SugarLet])

{-
showBinOp :: String -> String -> String -> String
showBinOp op x y = "("++ x ++ op ++ y ++ ")"

instance ShowF Value where
    showF (VInt i) = show i
    showF (VBool b) = show b
    showF (VPair x y) = showBinOp "," x y


instance ShowF Op where
    showF (Plus x y) = showBinOp "+" x y
    showF (Mult x y) = showBinOp "*" x y
    showF (If b x y) = "if " ++ b ++ " then " ++ x ++ " else " ++ y ++ " fi"
    showF (Eq x y) = showBinOp "==" x y
    showF (Lt x y) = showBinOp "<" x y
    showF (And x y) = showBinOp "&&" x y
    showF (Not x) = "~" ++ x
    showF (Proj ProjLeft x) = x ++ "!0"
    showF (Proj ProjRight x) = x ++ "!1"

instance ShowF ValueT where 
    showF TInt = "Int"
    showF TBool = "Bool"
    showF (TPair x y) = "(" ++ x ++ "," ++ y ++ ")"

instance ShowF Sugar where 
    showF (Neg x) = "- " ++ x
    showF (Minus x y) = "(" ++ x ++ "-" ++ y ++ ")"
    showF (Gt x y) = "(" ++ x ++ ">" ++ y ++ ")"
    showF (Or x y) = "(" ++ x ++ "||" ++ y ++ ")"
    showF (Impl x y) = "(" ++ x ++ "->" ++ y ++ ")"-}

class GenTyped f where
    genTypedAlg :: CoalgM Gen f BaseType
    genTypedAlg a = do dist <- genTypedAlg' a
                       frequency $ map (\(i,f) -> (i,return f)) dist
    genTypedAlg' :: BaseType -> Gen [(Int,f BaseType BaseType)]
    genTypedAlg' a = genTypedAlg a >>= \ g -> return [(1,g)]
{-
genTyped :: forall f . (Traversable f, GenTyped f) => BaseType -> Gen (Term f)
genTyped = run 
    where run :: BaseType -> Gen (Term f)
          run t = liftM Term $ genTypedAlg t >>= mapM (desize . run)

desize :: Gen a -> Gen a
desize gen = sized (\n -> resize (max 0 (n-1)) gen)

genSomeTyped :: (Traversable f, GenTyped f) => Gen (Term f)
genSomeTyped = arbitrary >>= genTyped

forAllTyped :: (GenTyped f, ShowF f, Testable prop, Traversable f) =>
               (Term f -> prop) -> Property
forAllTyped f = forAll genSomeTyped f


instance (GenTyped f, GenTyped g) => GenTyped (f :+: g) where
    genTypedAlg' t = do 
      left <- genTypedAlg' t
      right <- genTypedAlg' t
      let left' = map inl left
          right' = map inr right
      return (left' ++ right')
        where inl (i,gen) = (i,Inl gen)
              inr (i,gen) = (i,Inr gen)

instance GenTyped Value where
    genTypedAlg' (Term t) = run t
        where run TInt  = arbitrary >>= \i-> return [(1,VInt i)]
              run TBool = arbitrary >>= \b-> return [(1,VBool b)]
              run (TPair s t) = return [(1, VPair s t)]

instance GenTyped Op where
    genTypedAlg' ty = sized run
        where run n = do (ty1,ty2) <- arbitrary
                         other' <- other n
                         return $ other' ++ [(n,If iTBool ty ty),
                                   (n,Proj ProjLeft (iTPair ty ty1)),
                                   (n,Proj ProjRight (iTPair ty2 ty))]
              other n = case unTerm ty of
                        TInt -> return [(n,Plus iTInt iTInt),(n,Plus iTInt iTInt)]
                        TBool -> arbitrary >>= \t -> return
                                 [(n, Eq t t),
                                  (n,Lt iTInt iTInt),
                                  (n,And iTBool iTBool),
                                  (n,Not iTBool)]
                        TPair _ _ -> return []

instance GenTyped Sugar where
    genTypedAlg' (Term t) = sized (run t)
        where run TInt n = return [(5*n,Neg iTInt),(5*n,Minus iTInt iTInt)]
              run TBool n = return [(5*n,Gt iTInt iTInt),(5*n,Or iTBool iTBool),
                                 (5*n,Impl iTBool iTBool)]
              run TPair{} _ = return []-}