module Main where

import Criterion.Main
import qualified Functions.ALaCarte as A
import qualified Functions.Standard as S
import DataTypes.ALaCarte
import DataTypes.Standard
import DataTypes.Transform
import Data.ALaCarte.DeepSeq ()
import Control.DeepSeq

aExpr :: SugarExpr
aExpr = iIf ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))
            `iOr` ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))))
       ((iVInt 2 `iMinus` iVInt 1))
       (iVInt 3)

sExpr :: PExpr
sExpr = transSugar aExpr


main = rnf aExpr `seq` rnf sExpr `seq` run
    where run = defaultMain
                [bench "ALaCarte.desugar" (nf A.desugarExpr aExpr),
                 bench "Standard.desugar" (nf S.desugar sExpr),
                 bench "ALaCarte.desugarType" (nf A.desugarType aExpr),
                 bench "ALaCarte.desugarType'" (nf A.desugarType' aExpr),
                 bench "Standard.desugarType'" (nf S.desugarType sExpr),
                 bench "ALaCarte.desugarEval" (nf A.desugarEval aExpr),
                 bench "ALaCarte.desugarEval'" (nf A.desugarEval' aExpr),
                 bench "Standard.desugarEval" (nf S.desugarEval sExpr),
                 bench "ALaCarte.desugarEval2" (nf A.desugarEval2 aExpr),
                 bench "ALaCarte.desugarEval2'" (nf A.desugarEval2' aExpr),
                 bench "Standard.desugarEval2" (nf S.desugarEval2 sExpr)]