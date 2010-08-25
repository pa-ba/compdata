{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module Test.Utils where

import Data.ALaCarte
import Data.ALaCarte.Equality
import Data.ALaCarte.Arbitrary
import Data.ALaCarte.Show
import Data.DeriveTH


data Tree l e = Leaf l
              | UnNode l e
              | BinNode e l e
              | TerNode l e e e

$(derives [makeFunctor] [''Tree])
$(deriveShowF ''Tree)
$(deriveEqF ''Tree)
$(deriveArbitraryF ''Tree)

type Sig = Maybe :+: Tree Int :+: [] :+: (,) Int

type SigP = Sig :**: Int


instance Show (a -> b) where
    show _ = "<function>"