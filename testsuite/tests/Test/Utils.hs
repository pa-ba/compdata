{-# LANGUAGE TemplateHaskell, TypeOperators, FlexibleContexts, FlexibleInstances #-}

module Test.Utils where

import Data.ALaCarte
import Data.ALaCarte.Derive

import Data.Foldable


data Tree l e = Leaf l
              | UnNode l e
              | BinNode e l e
              | TerNode l e e e

data Pair a e = Pair a e

$(derive
  [instanceFunctor, instanceFoldable, instanceShowF, instanceEqF, instanceArbitraryF]
  [''Tree, ''Pair])

$(derive
  [smartConstructors]
  [''Tree, ''Pair, ''Maybe])


type Sig1 = Maybe :+: Tree Int :+: NilF 
type Sig2 = [] :+: Pair Int :+: NilF
type Sig = Sig1 :++: Sig2


type SigP = Sig :**: Int

instance EqF f => EqF (f :*: Int) where
    eqF (x :*: i) (y :*: j) = x `eqF` y && i == j

instance Show (a -> b) where
    show _ = "<function>"