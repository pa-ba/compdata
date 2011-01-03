module Main where

import Criterion.Main
import Functions
import DataTypes
import Data.ALaCarte.DeepSeq ()

testExpr :: SugarExpr
testExpr = iIf ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))
            `iOr` ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))))
       ((iVInt 2 `iMinus` iVInt 1))
       (iVInt 3)


main = defaultMain [bench "desugarType" (nf desugarType testExpr),
                    bench "desugarType'" (nf desugarType' testExpr),
                    bench "desugarEval" (nf desugarEval testExpr),
                    bench "desugarEval'" (nf desugarEval' testExpr),
                    bench "desugarEval2" (nf desugarEval2 testExpr),
                    bench "desugarEval2'" (nf desugarEval2' testExpr)]