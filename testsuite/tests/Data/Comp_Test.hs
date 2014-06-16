module Data.Comp_Test where

import Test.Framework 

import qualified Data.Comp.Equality_Test
import qualified Data.Comp.Examples_Test
import qualified Data.Comp.Variables_Test
import qualified Data.Comp.Multi_Test
import qualified Data.Comp.Subsume_Test

--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "Comp" [
         Data.Comp.Equality_Test.tests,
         Data.Comp.Examples_Test.tests,
         Data.Comp.Variables_Test.tests,
         Data.Comp.Multi_Test.tests,
         Data.Comp.Subsume_Test.tests
        ]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

