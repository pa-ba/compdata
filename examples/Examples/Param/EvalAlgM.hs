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
-- Monadic Expression Evaluation w/o PHOAS
--
-- The example illustrates how to use parametric compositional data types to
-- implement a small expression language, with a sub language of values, and a
-- monadic evaluation function mapping expressions to values. The lack for PHOAS
-- means that -- unlike the example in 'Examples.Param.EvalM' -- a monadic
-- algebra can be used.
--
-- The example is similar to the example from 'Examples.EvalM'.
--
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.
--
--------------------------------------------------------------------------------

module Examples.Param.EvalAlgM where

import Data.Comp.Param
import Data.Comp.Param.Traversable
import Data.Comp.Param.Derive
import Control.Monad (liftM)

-- Signature for values and operators
data Value a e = Const Int | Pair e e
data Op a e = Add e e | Mult e e | Fst e | Snd e

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [instanceDifunctor, instanceTraversable, instanceFoldable,
          instanceEqD, instanceShowD, smartConstructors]
         [''Value, ''Op])

-- Monadic term evaluation algebra
class EvalM f v where
  evalAlgM :: AlgM Maybe f (Term v)

instance (EvalM f v, EvalM g v) => EvalM (f :+: g) v where
  evalAlgM (Inl x) = evalAlgM x
  evalAlgM (Inr x) = evalAlgM x

-- Lift the monadic evaluation algebra to a monadic catamorphism
evalM :: (Ditraversable f Maybe (Term v), EvalM f v) => Term f -> Maybe (Term v)
evalM = cataM evalAlgM

instance (Value :<: v) => EvalM Value v where
  evalAlgM (Const n) = return $ iConst n
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

projC :: (Value :<: v) => Term v -> Maybe Int
projC v = case project v of
            Just (Const n) -> return n
            _ -> Nothing

projP :: (Value :<: v) => Term v -> Maybe (Term v, Term v)
projP v = case project v of
            Just (Pair x y) -> return (x,y)
            _ -> Nothing

-- Example: evalMEx = Just (iConst 5)
evalMEx :: Maybe (Term Value)
evalMEx = evalM ((iConst 1) `iAdd` (iConst 2 `iMult` iConst 2) :: Term Sig)