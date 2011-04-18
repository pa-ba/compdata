{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples.MultiParam where

import qualified Examples.MultiParam.Eval as Eval
import qualified Examples.MultiParam.EvalI as EvalI
{-import qualified Examples.MultiParam.EvalM as EvalM
import qualified Examples.MultiParam.EvalAlgM as EvalAlgM
import qualified Examples.MultiParam.DesugarEval as DesugarEval
import qualified Examples.MultiParam.DesugarPos as DesugarPos
import qualified Examples.MultiParam.Parsing as Parsing-}

import Data.Comp.MultiParam

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils





--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

tests = testGroup "Parametric Compositional Data Types" [
         testProperty "eval" evalTest,
         testProperty "evalI" evalITest{-,
         testProperty "evalM" evalMTest,
         testProperty "evalAlgM" evalAlgMTest,
         testProperty "desugarEval" desugarEvalTest,
         testProperty "desugarPos" desugarPosTest,
         testProperty "parsing" parsingTest-}
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

{-instance (EqD f, PEq p) => EqD (f :&: p) where
    eqD (v1 :&: p1) (v2 :&: p2) = do b1 <- peq p1 p2
                                     b2 <- eqD v1 v2
                                     return $ b1 && b2-}

evalTest = Eval.evalEx == Just (Eval.iConst 4)
evalITest = EvalI.evalEx == 4
{-evalMTest = EvalM.evalMEx == Just (EvalM.iConst 12)
evalAlgMTest = EvalAlgM.evalMEx == Just (EvalAlgM.iConst 5)
desugarEvalTest = DesugarEval.evalEx == Just (DesugarEval.iConst 720)
desugarPosTest = DesugarPos.desugPEx ==
                 DesugarPos.iAApp (DesugarPos.Pos 1 0)
                                  (DesugarPos.iALam (DesugarPos.Pos 1 0) Place)
                                  (DesugarPos.iALam (DesugarPos.Pos 1 1) $ \f ->
                                       DesugarPos.iAApp (DesugarPos.Pos 1 1)
                                                        (DesugarPos.iALam (DesugarPos.Pos 1 1) $ \x ->
                                                             DesugarPos.iAApp (DesugarPos.Pos 1 1) (Place f) (DesugarPos.iAApp (DesugarPos.Pos 1 1) (Place x) (Place x)))
                                                        (DesugarPos.iALam (DesugarPos.Pos 1 1) $ \x ->
                                                             DesugarPos.iAApp (DesugarPos.Pos 1 1) (Place f) (DesugarPos.iAApp (DesugarPos.Pos 1 1) (Place x) (Place x))))
parsingTest = Parsing.transEx == (Parsing.iLam $ \a -> Parsing.iApp (Parsing.iLam $ \b -> Parsing.iLam $ \c -> Place b) (Place a))-}