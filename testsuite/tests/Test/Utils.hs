{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Test.Utils where

import Data.ALaCarte
import Data.ALaCarte.Equality
import Data.ALaCarte.Arbitrary
import Data.ALaCarte.Show
import Data.DeriveTH

import Data.Foldable


data Tree l e = Leaf l
              | UnNode l e
              | BinNode e l e
              | TerNode l e e e

data Pair a e = Pair a e

$(derives [makeFunctor, makeFoldable] [''Tree, ''Pair])
$(deriveShowFs [''Tree, ''Pair])
$(deriveEqFs [''Tree, ''Pair])
$(deriveArbitraryFs [''Tree, ''Pair])



type Sig1 = Maybe :+: Tree Int :+: NilF 
type Sig2 = [] :+: Pair Int :+: NilF
type Sig = Sig1 :++: Sig2

type SigP = Sig :**: Int


instance Show (a -> b) where
    show _ = "<function>"