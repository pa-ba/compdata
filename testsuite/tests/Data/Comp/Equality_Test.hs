module Data.Comp.Equality_Test where


import Data.Comp
import Data.Comp.Equality ()
import Data.Comp.Arbitrary ()
import Data.Comp.Show ()

import Test.Framework
import Test.Framework.Providers.QuickCheck2
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
          _with = (cxt :: Context SigP Int, f :: Int -> Int)
