module Main where

import Criterion.Main
import qualified Functions.ALaCarte as A
import qualified Functions.Standard as S
import DataTypes.ALaCarte
import DataTypes.Standard
import DataTypes.Transform
import Data.ALaCarte
import Data.ALaCarte.DeepSeq ()
import Control.DeepSeq
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import System.Random

aExpr :: SugarExpr
aExpr = iIf ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))
            `iOr` ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))))
       ((iVInt 2 `iMinus` iVInt 1))
       (iVInt 3)

sExpr :: PExpr
sExpr = transSugar aExpr


main = do b1 <- genExprs 5
          b2 <- genExprs 10
          b3 <- genExprs 20
          let b0 = getBench (sExpr, aExpr, "hand-written")
          defaultMain [b0,b1,b2,b3]
    where genExprs s = do
            rand <- getStdGen
            let ty = unGen arbitrary rand s
            putStr "size of the type term: "
            print $ size ty
            print $ ty
            let aExpr = unGen (genTyped ty) rand s
                sExpr = transSugar aExpr
            putStr "size of the input term: "
            print $ size aExpr
            putStr "does it type check: "
            print (A.desugarType aExpr == Right ty)
            return $ getBench (sExpr,aExpr, "random (depth: " ++ show s ++ ", size: "++ show (size aExpr) ++ ")")
          getBench (sExpr,aExpr,n) = rnf aExpr `seq` rnf sExpr `seq` getBench' (sExpr, aExpr,n)
          getBench' (sExpr, aExpr,n) = bgroup n
                [
                 -- bench "ALaCarte.desugar" (nf A.desugarExpr aExpr),
                 -- bench "Standard.desugar" (nf S.desugar sExpr),
                 -- bench "ALaCarte.desugarType" (nf A.desugarType aExpr),
                 -- bench "ALaCarte.desugarType'" (nf A.desugarType' aExpr),
                 -- bench "Standard.desugarType" (nf S.desugarType sExpr),
                 -- bench "ALaCarte.typeSugar" (nf A.typeSugar aExpr),
                 -- bench "Standard.typeSugar" (nf S.typeSugar sExpr),
                 -- bench "ALaCarte.desugarType2" (nf A.desugarType2 aExpr),
                 -- bench "ALaCarte.desugarType2'" (nf A.desugarType2' aExpr),
                 -- bench "Standard.desugarType2" (nf S.desugarType2 sExpr),
                 -- bench "ALaCarte.typeSugar2" (nf A.typeSugar2 aExpr),
                 -- bench "Standard.typeSugar2" (nf S.typeSugar2 sExpr),
                 -- bench "ALaCarte.desugarEval" (nf A.desugarEval aExpr),
                 -- bench "ALaCarte.desugarEval'" (nf A.desugarEval' aExpr),
                 -- bench "Standard.desugarEval" (nf S.desugarEval sExpr),
                 -- bench "ALaCarte.evalSugar" (nf A.evalSugar aExpr),
                 -- bench "ALaCarte.evalDirect" (nf A.evalDirectE aExpr),
                 -- bench "Standard.evalSugar" (nf S.evalSugar sExpr),
                 -- bench "ALaCarte.desugarEval2" (nf A.desugarEval2 aExpr),
                 -- bench "ALaCarte.desugarEval2'" (nf A.desugarEval2' aExpr),
                 -- bench "Standard.desugarEval2" (nf S.desugarEval2 sExpr),
                 -- bench "ALaCarte.evalSugar2" (nf A.evalSugar2 aExpr),
                 -- bench "ALaCarte.evalDirect2" (nf A.evalDirectE2 aExpr),
                 -- bench "Standard.evalSugar2" (nf S.evalSugar2 sExpr),
                 bench "ALaCarte.contVar" (nf (A.contVar 10) aExpr),
                 bench "ALaCarte.contVar'" (nf (A.contVar' 10) aExpr),
                 bench "ALaCarte.contVarGen" (nf (A.contVarGen 10) aExpr),
                 bench "Standard.contVar" (nf (S.contVar 10) sExpr),
                 bench "Standard.contVarGen" (nf (S.contVarGen 10) sExpr),
                 bench "ALaCarte.freeVars" (nf A.freeVars aExpr),
                 bench "ALaCarte.freeVars'" (nf A.freeVars' aExpr),
                 bench "ALaCarte.freeVarsGen" (nf A.freeVarsGen aExpr),
                 bench "Standard.freeVars" (nf S.freeVars sExpr),
                 bench "Standard.freeVarsGen" (nf S.freeVarsGen sExpr),
                 bench "Standard.freeVarsGen" (nf S.freeVarsGen sExpr)]

          

{-
TODO 
 - benchmark generic functions (e.g. size, depth, breadth)
 - benchmark highly selective functions (e.g. freeVariables, substitution application)

-}