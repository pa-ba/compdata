{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples.Param where

import qualified Examples.Param.Eval as Eval
import qualified Examples.Param.EvalM as EvalM
import qualified Examples.Param.EvalAlgM as EvalAlgM
import qualified Examples.Param.DesugarEval as DesugarEval
import qualified Examples.Param.DesugarPos as DesugarPos
import qualified Examples.Param.Nominals as Nominals
import qualified Examples.Param.Graph as Graph
import qualified Examples.Param.Lambda as Lambda

import Data.Comp.Param

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils





--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

tests = testGroup "Parametric Compositional Data Types" [
         testProperty "eval" evalTest,
         testProperty "evalM" evalMTest,
         testProperty "evalAlgM" evalAlgMTest,
         testProperty "desugarEval" desugarEvalTest,
         testProperty "desugarPos" desugarPosTest,
         testProperty "nominals" nominalsTest,
         testProperty "graph" graphTest,
         testProperty "lambda" lambdaTest
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

instance (EqD f, PEq p) => EqD (f :&: p) where
    eqD (v1 :&: p1) (v2 :&: p2) = do b1 <- peq p1 p2
                                     b2 <- eqD v1 v2
                                     return $ b1 && b2

evalTest = Eval.evalEx == Just (Eval.iConst 4)
evalMTest = EvalM.evalMEx == Just (EvalM.iConst 12)
evalAlgMTest = EvalAlgM.evalMEx == Just (EvalAlgM.iConst 5)
desugarEvalTest = DesugarEval.evalEx == Just (DesugarEval.iConst 720)
desugarPosTest = DesugarPos.desugPEx ==
                 DesugarPos.iAApp (DesugarPos.Pos 1 0)
                                  (DesugarPos.iALam (DesugarPos.Pos 1 0) id)
                                  (DesugarPos.iALam (DesugarPos.Pos 1 1) $ \f ->
                                       DesugarPos.iAApp (DesugarPos.Pos 1 1)
                                                        (DesugarPos.iALam (DesugarPos.Pos 1 1) $ \x ->
                                                             DesugarPos.iAApp (DesugarPos.Pos 1 1) f (DesugarPos.iAApp (DesugarPos.Pos 1 1) x x))
                                                        (DesugarPos.iALam (DesugarPos.Pos 1 1) $ \x ->
                                                             DesugarPos.iAApp (DesugarPos.Pos 1 1) f (DesugarPos.iAApp (DesugarPos.Pos 1 1) x x)))
nominalsTest = Nominals.en == Nominals.en' && Nominals.ep == Nominals.ep'
graphTest = Graph.alphaTest && Graph.n == 5 && Graph.f == [0,2,1,2] && Graph.flatG Graph.g0' == ["0","2","1","2"]
lambdaTest = Lambda.e' == (Lambda.iLam (\a -> a)) `iApp` (Lambda.iLam (\a -> a)) && Lambda.e1' == Lambda.iLam (\a -> a `Lambda.iApp` Lambda.iLam (\b -> Lambda.iLam (\c -> b `Lambda.iApp` b `Lambda.iApp` c)))