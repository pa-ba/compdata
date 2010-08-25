module Data.ALaCarte.Equality_Test where


import Data.ALaCarte
import Data.ALaCarte.Equality
import Data.ALaCarte.Arbitrary
import Data.ALaCarte.Show

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils





--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "Equality" [
         testProperty "prop_eqMod_fmap" prop_eqMod_fmap
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_eqMod_fmap cxt f = case eqMod cxt cxt' of
                   Nothing -> False
                   Just list -> all (uncurry (==)) $ map (\(x,y)->(f x,y)) list
    where cxt' = fmap f cxt 
          with = (cxt :: Context Sig Int, f :: Int -> Int)
