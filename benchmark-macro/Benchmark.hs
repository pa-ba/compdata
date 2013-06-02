{-# LANGUAGE TypeOperators, DeriveFunctor, DeriveTraversable, DeriveFoldable, TemplateHaskell, GADTs #-}

module Main where

import Criterion.Main
import Data.Comp.Derive
import Data.Comp.DeepSeq ()
import Data.Comp.Arbitrary ()
import Data.Comp.Show ()
import Data.Comp

import qualified Functions.Mono as M
import qualified DataTypes.Mono as M



benchmarks :: String -> Term M.ArithLet -> String -> Term M.ArithExc -> Benchmark
benchmarks n t n' t' = rnf t `seq` rnf t' `seq` getBench
    where getBench = bgroup "" [letBench, excBench]
          letBench = bgroup n
                     [ inlineAnnBench
                     , annInlineBench
                     ]
          excBench = bgroup n' 
                     [ compAnnBench
                     , annCompBench]
          inlineAnnBench = bgroup "inlineAnn" 
                           [ bench "fused" (nf M.inlineAnnFuse t) 
                           , bench "seq" (nf M.inlineAnnSeq t)
                           , bench "implicit, fused" (nf M.inlineAnnImpFuse t) 
                           , bench "implicit, seq" (nf M.inlineAnnImpSeq t) ]
          annInlineBench = bgroup "annInline" 
                           [ bench "fused" (nf M.annInlineFuse t) 
                           , bench "seq" (nf M.annInlineSeq t)
                           , bench "implicit, fused)" (nf M.annInlineImpFuse t) 
                           , bench "implicit, seq" (nf M.annInlineImpSeq t) ]
          compAnnBench = bgroup "compAnn"
                         [ bench "fused" (nf M.compAnnFuse t')
                         , bench "seq" (nf M.compAnnSeq t')]
          annCompBench = bgroup "annComp"
                         [ bench "fused" (nf M.annCompFuse t')
                         , bench "seq" (nf M.annCompSeq t')]

genExpr :: Int -> IO Benchmark
genExpr s = do
  let t = M.exprAL s
  let t' = M.exprAE s
  putStr "size of the term: "
  let termsize = size t
  let termsize' = size t'
  print termsize
  putStr "size of the other term: "
  print termsize'
  return $ benchmarks ("term size="++ show termsize) t ("term size="++ show termsize') t'

main = do b0 <- genExpr 11
          b1 <- genExpr 8
          b2 <- genExpr 4
          defaultMain [b0, b1,b2]
