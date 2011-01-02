module Main where

import Criterion.Main
import Data.ALaCarte

fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

main = defaultMain [bench "foo" (whnf fib 20)]