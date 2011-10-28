{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.EvalAlgM
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Monadic Expression Evaluation without PHOAS
--
-- The example illustrates how to use parametric compositional data types to
-- implement a small expression language, with a sub language of values, and a
-- monadic evaluation function mapping expressions to values. The lack for PHOAS
-- means that -- unlike the example in 'Examples.Param.EvalM' -- a monadic
-- algebra can be used.
--
--------------------------------------------------------------------------------

module Examples.Param.EvalAlgM where

import Data.Comp.Param
import Data.Comp.Param.Show ()
import Data.Comp.Param.Ditraversable
import Data.Comp.Param.Derive
import Control.Monad (liftM)

-- Signature for values and operators
data Value a e = Const Int | Pair e e
data Op a e    = Add e e | Mult e e | Fst e | Snd e

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [makeDifunctor, makeDitraversable,
          makeEqD, makeOrdD, makeShowD, smartConstructors]
         [''Value, ''Op])

-- Monadic term evaluation algebra
class EvalM f v where
  evalAlgM :: AlgM Maybe f (Trm v a)

$(derive [liftSum] [''EvalM])

-- Lift the monadic evaluation algebra to a monadic catamorphism
evalM :: (Ditraversable f Maybe, EvalM f v) => Term f -> Maybe (Term v)
evalM t = trmM (cataM evalAlgM t)

instance (Value :<: v) => EvalM Value v where
  evalAlgM (Const n)  = return $ iConst n
  evalAlgM (Pair x y) = return $ iPair x y

instance (Value :<: v) => EvalM Op v where
  evalAlgM (Add x y)  = do n1 <- projC x
                           n2 <- projC y
                           return $ iConst $ n1 + n2
  evalAlgM (Mult x y) = do n1 <- projC x
                           n2 <- projC y
                           return $ iConst $ n1 * n2
  evalAlgM (Fst v)    = liftM fst $ projP v
  evalAlgM (Snd v)    = liftM snd $ projP v

projC :: (Value :<: v) => Trm v a -> Maybe Int
projC v = case project v of
            Just (Const n) -> return n
            _ -> Nothing

projP :: (Value :<: v) => Trm v a -> Maybe (Trm v a, Trm v a)
projP v = case project v of
            Just (Pair x y) -> return (x,y)
            _ -> Nothing

-- Example: evalMEx = Just (iConst 5)
evalMEx :: Maybe (Term Value)
evalMEx = evalM (Term $ iConst 1 `iAdd` (iConst 2 `iMult` iConst 2) :: Term Sig)