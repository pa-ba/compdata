module Main where

import qualified Functions.Comp as A
import qualified Functions.Standard as S
import DataTypes.Comp
import DataTypes.Transform
import Test.QuickCheck
import Data.List

main = mapM_ (quickCheckWith stdArgs{maxSize=10}) allProp

allProp = map forAllTyped [prop_desug, prop_desugAlg, prop_desugType, prop_desugType', prop_typeSugar, prop_desugType2, prop_desugType2', prop_typeSugar2, prop_desugEval, prop_desugEval', prop_evalSugar, prop_evalSugar, prop_evalDirect, prop_desugEval2, prop_desugEval2', prop_evalSugar2, prop_evalDirect2, prop_freeVars, prop_freeVars', prop_freeVarsGen, prop_freeVarsGenS]
          ++ map forAllTyped [prop_contVar, prop_contVar', prop_contVarGen, prop_contVarGenS]

prop_desug x = transCore (A.desugExpr x) == S.desug (transSugar x)

prop_desugAlg x = transCore (A.desugExpr2 x) == S.desug (transSugar x)

prop_desugType x = fmap transType (A.desugType x) == S.desugType (transSugar x)

prop_desugType' x = fmap transType (A.desugType' x) == S.desugType (transSugar x)

prop_typeSugar x = fmap transType (A.typeSugar x) == S.typeSugar (transSugar x)

prop_desugType2 x = transType (A.desugType2 x) == S.desugType2 (transSugar x)

prop_desugType2' x = transType (A.desugType2' x) == S.desugType2 (transSugar x)

prop_typeSugar2 x = transType (A.typeSugar2 x) == S.typeSugar2 (transSugar x)

prop_desugEval x = fmap transVal (A.desugEval x) == S.desugEval (transSugar x)

prop_desugEval' x = fmap transVal (A.desugEval' x) == S.desugEval (transSugar x)

prop_evalSugar x = fmap transVal (A.evalSugar x) == S.evalSugar (transSugar x)

prop_evalDirect x = fmap transVal (A.evalDirect x) == S.evalSugar (transSugar x)

prop_desugEval2 x = transVal (A.desugEval2 x) == S.desugEval2 (transSugar x)

prop_desugEval2' x = transVal (A.desugEval2' x) == S.desugEval2 (transSugar x)

prop_evalSugar2 x = transVal (A.evalSugar2 x) == S.evalSugar2 (transSugar x)

prop_evalDirect2 x = transVal (A.evalDirect2 x) == S.evalSugar2 (transSugar x)

prop_contVar x v = A.contVar v x == S.contVar v (transSugar x)

prop_contVar' x v = A.contVar' v x == S.contVar v (transSugar x)

prop_contVarGen x v = A.contVarGen v x == S.contVar v (transSugar x)

prop_contVarGenS x v = S.contVarGen v (transSugar x) == S.contVar v (transSugar x)

prop_freeVars x = A.freeVars x == S.freeVars (transSugar x)

prop_freeVars' x = A.freeVars' x == S.freeVars (transSugar x)

prop_freeVarsGen x = sort (A.freeVarsGen x) == sort (S.freeVars (transSugar x))

prop_freeVarsGenS x = S.freeVarsGen (transSugar x) == S.freeVars (transSugar x)