{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Common
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Common definitions used in examples.
--
--------------------------------------------------------------------------------

module Examples.Common where

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Show ()
import Data.Comp.Equality ()

-- Signature for values and operators
data Value a = Const Int | Pair a a
data Op a    = Add a a | Mult a a | Fst a | Snd a

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [makeFunctor, makeTraversable, makeFoldable,
          makeEqF, makeShowF, smartConstructors, smartAConstructors]
         [''Value, ''Op])