module Data.Comp_Test where


import Data.Comp
import Data.Comp.Equality
import Data.Comp.Arbitrary ()
import Data.Comp.Show ()

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils

import qualified Data.Comp.Equality_Test


--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "Comp" [
         Data.Comp.Equality_Test.tests
        ]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

