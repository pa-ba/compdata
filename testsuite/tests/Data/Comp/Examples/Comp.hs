{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples.Comp where

import qualified Examples.Eval as Eval
import qualified Examples.EvalM as EvalM
import qualified Examples.DesugarEval as DesugarEval
import qualified Examples.DesugarPos as DesugarPos

import Data.Comp

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils





--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

tests = testGroup "Compositional Data Types" [
         testProperty "eval" evalTest,
         testProperty "evalM" evalMTest,
         testProperty "desugarEval" desugarEvalTest,
         testProperty "desugarPos" desugarPosTest
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

instance (EqF f, Eq p) => EqF (f :&: p) where
    eqF (v1 :&: p1) (v2 :&: p2) = p1 == p2 && v1 `eqF` v2

evalTest = Eval.evalEx == Eval.iConst 5
evalMTest = EvalM.evalMEx == Just (EvalM.iConst 5)
desugarEvalTest = DesugarEval.evalEx == DesugarEval.iPair (DesugarEval.iConst 2) (DesugarEval.iConst 1)
desugarPosTest = DesugarPos.desugPEx ==
                 DesugarPos.iPPair
                               (DesugarPos.Pos 1 0)
                               (DesugarPos.iPSnd
                                              (DesugarPos.Pos 1 0)
                                              (DesugarPos.iPPair
                                                             (DesugarPos.Pos 1 1)
                                                             (DesugarPos.iPConst (DesugarPos.Pos 1 2) 1)
                                                             (DesugarPos.iPConst (DesugarPos.Pos 1 3) 2)))
                               (DesugarPos.iPFst
                                              (DesugarPos.Pos 1 0)
                                              (DesugarPos.iPPair
                                                             (DesugarPos.Pos 1 1)
                                                             (DesugarPos.iPConst (DesugarPos.Pos 1 2) 1)
                                                             (DesugarPos.iPConst (DesugarPos.Pos 1 3) 2)))