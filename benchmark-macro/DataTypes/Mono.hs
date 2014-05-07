{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable, TemplateHaskell,
  FlexibleContexts, ConstraintKinds #-}

module DataTypes.Mono where

import Data.Comp.Derive
import Data.Comp

type Var = String

data ArithLet a = Add a a | Mult a a | Sub a a | Val Int | Let Var a a | Var Var
               deriving (Show, Functor, Foldable, Traversable)

data ArithExc a = Add' a a | Val' Int | Throw | Catch a a
             deriving (Show, Functor, Foldable, Traversable)

data Code a = PUSH Int a 
             | ADD a
             | THROW
             | MARK a a
             | UNMARK a
             | NIL
             deriving (Show, Functor, Foldable, Traversable)


$(derive
  [makeShowF, makeEqF, makeNFDataF, makeArbitraryF, smartConstructors]
  [''ArithLet, ''ArithExc, ''Code])


exprAL :: Int -> Term ArithLet 
exprAL 0 = iVal 4
exprAL n = iLet "x" e1 e2
    where e1 = (iVal 1 `iSub` iVal 2) `iAdd` iLet "y" e3 e4
          e2 = iVar "x" `iMult` iVal 4 `iAdd` iLet "z" e5 e6 `iSub` exprAL (n-1)
          e3 = iVal 2 `iAdd` iVal 3
          e4 = iVar "y" `iAdd` iVar "y"
          e5 = iVar "x" `iMult` iVar "x"
          e6 = (iVar "x" `iSub` iVar "z") `iAdd` exprAL (n-1)

exprAE :: Int -> Term ArithExc
exprAE 0 = iVal' 3
exprAE n = iVal' 1 `iAdd'` iCatch (exprAE (n-1) `iAdd'` iThrow) (iVal' 2 `iAdd'` exprAE (n-1))
