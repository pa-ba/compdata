{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples_Test where

import qualified Data.Comp.Examples.Comp as C
import qualified Data.Comp.Examples.Multi as M
import qualified Data.Comp.Examples.Param as P
import qualified Data.Comp.Examples.MultiParam as MP

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils

tests = testGroup "Examples" [
         C.tests,
         M.tests,
         P.tests,
         MP.tests
       ]