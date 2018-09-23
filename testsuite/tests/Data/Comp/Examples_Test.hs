{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples_Test where

import qualified Data.Comp.Examples.Comp as C
import qualified Data.Comp.Examples.Multi as M

import Test.Framework

tests = testGroup "Examples" [
         C.tests,
         M.tests
       ]
