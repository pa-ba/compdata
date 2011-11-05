{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples.Param where

import Examples.Param.Nominals as Nominals
import Examples.Param.Graph as Graph

import Data.Comp.Param

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils





--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

tests = testGroup "Parametric Compositional Data Types" [
         testProperty "nominals" nominalsTest,
         testProperty "graph" graphTest
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

instance (EqD f, PEq p) => EqD (f :&: p) where
    eqD (v1 :&: p1) (v2 :&: p2) = do b1 <- peq p1 p2
                                     b2 <- eqD v1 v2
                                     return $ b1 && b2

nominalsTest = en == en' && ep == ep'
graphTest = g == g && n == 5 && f == [0,2,1,2]