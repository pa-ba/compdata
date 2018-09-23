{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples.Comp where

import Examples.Common
import Examples.Eval as Eval
import Examples.EvalM as EvalM
import Examples.Desugar as Desugar

import Data.Comp

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit


--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

tests = testGroup "Compositional Data Types" [
         testCase "eval" evalTest,
         testCase "evalM" evalMTest,
         testCase "desugarEval" desugarEvalTest,
         testCase "desugarPos" desugarPosTest
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

instance (EqF f, Eq p) => EqF (f :&: p) where
    eqF (v1 :&: p1) (v2 :&: p2) = p1 == p2 && v1 `eqF` v2

evalTest = Eval.evalEx @=? iConst 5
evalMTest = evalMEx @=? Just (iConst 5)
desugarEvalTest = Desugar.evalEx @=? iPair (iConst 2) (iConst 1)
desugarPosTest = desugPEx @=? iAPair (Pos 1 0)
                                    (iASnd (Pos 1 0)
                                           (iAPair (Pos 1 1)
                                                   (iAConst (Pos 1 2) 1)
                                                   (iAConst (Pos 1 3) 2)))
                                    (iAFst (Pos 1 0)
                                           (iAPair (Pos 1 1)
                                                   (iAConst (Pos 1 2) 1)
                                                   (iAConst (Pos 1 3) 2)))
