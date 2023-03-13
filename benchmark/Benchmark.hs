module Main where

import Criterion.Main
import qualified Functions.Comp as A
import qualified Functions.Standard as S
import DataTypes.Comp as DC
import DataTypes.Standard as DS
import DataTypes.Transform
import Data.Comp
import Data.Comp.DeepSeq ()
import Control.DeepSeq
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Random


aExpr :: SugarExpr
aExpr = iIf ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))
            `iOr` ((iVInt 1 `iGt` (iVInt 2 `iMinus` iVInt 1))))
       ((iVInt 2 `iMinus` iVInt 1))
       (iVInt 3)

sExpr :: PExpr
sExpr = transSugar aExpr


sfCoalg :: Coalg SugarSig Int
sfCoalg 0 = inj $ VInt 1
sfCoalg n = let n' = n-1 in inj $ Plus n' n'

sfGen' :: Int -> SugarExpr
sfGen'  = ana' sfCoalg

sfGen :: Int -> SugarExpr
sfGen  = ana sfCoalg

shortcutFusion :: Benchmark
shortcutFusion = bgroup "shortcut-fusion" [
                  bench "eval without fusion" (nf (A.evalSugar2 . sfGen) depth),
                  bench "eval with fusion" (nf (A.evalSugar2 . sfGen') depth)
                  ]
    where depth = 15

standardBenchmarks :: (PExpr, SugarExpr, String) -> Benchmark
standardBenchmarks  (sExpr,aExpr,n) = rnf aExpr `seq` rnf sExpr `seq` getBench n
    where getBench n = bgroup n paperBenchmarks
          -- these are the benchmarks for evaluation
          _evalBenchmarks = [
                 bench "evalDesug" (nf A.desugEval2 aExpr),
                 bench "evalDesug (fusion)" (nf A.desugEval2' aExpr),
                 bench "evalDesug (comparison)" (nf S.desugEval2 sExpr),
                 bench "evalDesugM" (nf A.desugEval aExpr),
                 bench "evalDesugT" (nf A.desugEvalT aExpr),
                 bench "evalDesugM (fusion)" (nf A.desugEval' aExpr),
                 bench "evalDesugT (fusion)" (nf A.desugEvalT' aExpr),
                 bench "evalDesugM (comparison)" (nf S.desugEval sExpr),
                 bench "eval" (nf A.evalSugar2 aExpr),
                 bench "evalDirect" (nf A.evalDirectE2 aExpr),
                 bench "eval[Direct] (comparison)" (nf S.evalSugar2 sExpr),
                 bench "evalM" (nf A.evalSugar aExpr),
                 bench "evalT" (nf A.evalSugarT aExpr),
                 bench "evalDirectM" (nf A.evalDirectE aExpr),
                 bench "eval[Direct]M (comparison)" (nf S.evalSugar sExpr)]
          -- these are the benchmarks from the WGP '11 paper
          paperBenchmarks = [
                 bench "desugHom" (nf A.desugExpr aExpr),
                 bench "desugCata" (nf A.desugExpr2 aExpr),
                 bench "desug[Hom,Cata] (comparison)" (nf S.desug sExpr),
                 bench "inferDesug" (nf A.desugType2 aExpr),
                 bench "inferDesug (fusion)" (nf A.desugType2' aExpr),
                 bench "inferDesug (comparison)" (nf S.desugType2 sExpr),
                 bench "inferDesugM" (nf A.desugType aExpr),
                 bench "inferDesugM (fusion)" (nf A.desugType' aExpr),
                 bench "inferDesugM (comparison)" (nf S.desugType sExpr),
                 bench "infer" (nf A.typeSugar2 aExpr),
                 bench "infer (comparison)" (nf S.typeSugar2 sExpr),
                 bench "inferM" (nf A.typeSugar aExpr),
                 bench "inferM (comparison)" (nf S.typeSugar sExpr),
                 bench "evalDesug" (nf A.desugEval2 aExpr),
                 bench "evalDesug (fusion)" (nf A.desugEval2' aExpr),
                 bench "evalDesug (comparison)" (nf S.desugEval2 sExpr),
                 bench "evalDesugM" (nf A.desugEval aExpr),
                 bench "evalDesugM (fusion)" (nf A.desugEval' aExpr),
                 bench "evalDesugM (comparison)" (nf S.desugEval sExpr),
                 bench "eval" (nf A.evalSugar2 aExpr),
                 bench "evalDirect" (nf A.evalDirectE2 aExpr),
                 bench "eval[Direct] (comparison)" (nf S.evalSugar2 sExpr),
                 bench "evalM" (nf A.evalSugar aExpr),
                 bench "evalDirectM" (nf A.evalDirectE aExpr),
                 bench "eval[Direct]M (comparison)" (nf S.evalSugar sExpr),
                 bench "contVar" (nf (A.contVar' 10) aExpr),
                 bench "contVarG" (nf (A.contVarGen 10) aExpr),
                 bench "contVarU" (nf (S.contVarGen 10) sExpr),
                 bench "contVar (comparison)" (nf (S.contVar 10) sExpr),
                 bench "freeVars" (nf A.freeVars' aExpr),
                 bench "freeVarsG" (nf A.freeVarsGen aExpr),
                 bench "freeVarsU" (nf S.freeVarsGen sExpr),
                 bench "freeVars (comparison)" (nf S.freeVars sExpr)]
          -- these are all the benchmarks
          _allBenchmarks = [
                 bench "Comp.desug" (nf A.desugExpr aExpr),
                 bench "Comp.desug'" (nf A.desugExpr' aExpr),
                 bench "Comp.desugAlg" (nf A.desugExpr2 aExpr),
                 bench "Standard.desug" (nf S.desug sExpr),
                 bench "Standard.desug'" (nf S.desug' sExpr),
                 bench "Comp.desugType" (nf A.desugType aExpr),
                 bench "Comp.desugType'" (nf A.desugType' aExpr),
                 bench "Standard.desugType" (nf S.desugType sExpr),
                 bench "Comp.typeSugar" (nf A.typeSugar aExpr),
                 bench "Standard.typeSugar" (nf S.typeSugar sExpr),
                 bench "Comp.desugType2" (nf A.desugType2 aExpr),
                 bench "Comp.desugType2'" (nf A.desugType2' aExpr),
                 bench "Standard.desugType2" (nf S.desugType2 sExpr),
                 bench "Comp.typeSugar2" (nf A.typeSugar2 aExpr),
                 bench "Standard.typeSugar2" (nf S.typeSugar2 sExpr),
                 bench "Comp.desugEval" (nf A.desugEval aExpr),
                 bench "Comp.desugEval'" (nf A.desugEval' aExpr),
                 bench "Standard.desugEval" (nf S.desugEval sExpr),
                 bench "Comp.evalSugar" (nf A.evalSugar aExpr),
                 bench "Comp.evalDirect" (nf A.evalDirectE aExpr),
                 bench "Standard.evalSugar" (nf S.evalSugar sExpr),
                 bench "Comp.desugEval2" (nf A.desugEval2 aExpr),
                 bench "Comp.desugEval2'" (nf A.desugEval2' aExpr),
                 bench "Standard.desugEval2" (nf S.desugEval2 sExpr),
                 bench "Comp.evalSugar2" (nf A.evalSugar2 aExpr),
                 bench "Comp.evalDirect2" (nf A.evalDirectE2 aExpr),
                 bench "Standard.evalSugar2" (nf S.evalSugar2 sExpr),
                 bench "Comp.contVar" (nf (A.contVar 10) aExpr),
                 bench "Comp.contVar'" (nf (A.contVar' 10) aExpr),
                 bench "Comp.contVarGen" (nf (A.contVarGen 10) aExpr),
                 bench "Standard.contVar" (nf (S.contVar 10) sExpr),
                 bench "Standard.contVarGen" (nf (S.contVarGen 10) sExpr),
                 bench "Comp.freeVars" (nf A.freeVars aExpr),
                 bench "Comp.freeVars'" (nf A.freeVars' aExpr),
                 bench "Comp.freeVarsGen" (nf A.freeVarsGen aExpr),
                 bench "Standard.freeVars" (nf S.freeVars sExpr),
                 bench "Standard.freeVarsGen" (nf S.freeVarsGen sExpr)
                                      ]

randStdBenchmarks :: Int -> IO Benchmark
randStdBenchmarks s = do
  rand <- newQCGen
  let ty = unGen arbitrary rand s
  putStr "size of the type term: "
  print $ size ty
  print $ ty
  let aExpr = unGen (genTyped ty) rand s
      sExpr = transSugar aExpr
  putStr "size of the input term: "
  print $ size aExpr
  putStr "does it type check: "
  print (A.desugType aExpr == Right ty)
  return $ standardBenchmarks (sExpr,aExpr, "random (depth: " ++ show s ++ ", size: "++ show (size aExpr) ++ ")")


main = do b1 <- randStdBenchmarks 5
          b2 <- randStdBenchmarks 10
          b3 <- randStdBenchmarks 20
          let b0 = standardBenchmarks (sExpr, aExpr, "hand-written")
          defaultMain $ [b0,b1,b2,b3]
