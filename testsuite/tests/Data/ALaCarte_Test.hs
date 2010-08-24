{-# LANGUAGE TemplateHaskell #-}

module Data.ALaCarte_Test where


import Data.ALaCarte
import Data.ALaCarte.Equality
import Data.ALaCarte.Arbitrary
import Data.ALaCarte.Show

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.QuickCheck.Property

--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "ALaCarte" [
         testProperty "prop_EqF" prop_EqF
        ]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_EqF cxt = case eqMod cxt cxt' of
                   Nothing -> False
                   Just list -> all (uncurry (==)) $ map (\(x,y)->(x,f y)) list
    where cxt' = fmap f cxt 
          f = (+1)
          with = (cxt :: Context Maybe Int, f :: Int -> Int)
