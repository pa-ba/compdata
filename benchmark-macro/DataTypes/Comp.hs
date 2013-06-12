{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable, TemplateHaskell, FlexibleContexts #-}

module DataTypes.Comp where

import Data.Comp.Derive

type Var = String

data Arith a = Add a a | Val Int 
               deriving (Show, Functor, Foldable, Traversable)

data Let a = Let Var a a | Var Var
                           deriving (Show, Functor, Foldable, Traversable)
data Exc a = Throw | Catch a a
             deriving (Show, Functor, Foldable, Traversable)

data Code a = PUSH Int a 
             | ADD a
             | THROW
             | MARK a a
             | UNMARK a
             | NIL



$(derive
  [makeEqF, makeNFDataF, makeArbitraryF, smartConstructors]
  [''Arith, ''Let, ''Exc])
