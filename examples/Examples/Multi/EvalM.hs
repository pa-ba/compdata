{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Multi.EvalM
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Monadic Expression Evaluation
--
-- The example illustrates how to use generalised compositional data types to
-- implement a small expression language, with a sub language of values, and a 
-- monadic evaluation function mapping expressions to values.
--
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@,
-- @GADTs@. Besides, GCH 7 is required.
--
--------------------------------------------------------------------------------

module Examples.Multi.EvalM where

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Derive
import Control.Monad (liftM)

-- Signature for values and operators
data Value e l where
  Const  ::        Int -> Value e Int
  Pair   :: e s -> e t -> Value e (s,t)
data Op e l where
  Add, Mult  :: e Int -> e Int   -> Op e Int
  Fst        ::          e (s,t) -> Op e s
  Snd        ::          e (s,t) -> Op e t

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell (GHC 7 needed)
$(derive [instanceHFunctor, instanceHTraversable, instanceHFoldable,
          instanceHEqF, instanceHShowF, smartConstructors]
         [''Value, ''Op])

-- Monadic term evaluation algebra
class EvalM f v where
  evalAlgM :: AlgM Maybe f (Term v)

instance (EvalM f v, EvalM g v) => EvalM (f :+: g) v where
  evalAlgM (Inl x) = evalAlgM x
  evalAlgM (Inr x) = evalAlgM x

evalM :: (HTraversable f, EvalM f v) => Term f l -> Maybe (Term v l)
evalM = cataM evalAlgM

instance (Value :<: v) => EvalM Value v where
  evalAlgM = return . inject

instance (Value :<: v) => EvalM Op v where
  evalAlgM (Add x y)  = do n1 <- projC x
                           n2 <- projC y
                           return $ iConst $ n1 + n2
  evalAlgM (Mult x y) = do n1 <- projC x
                           n2 <- projC y
                           return $ iConst $ n1 * n2
  evalAlgM (Fst v)    = liftM fst $ projP v
  evalAlgM (Snd v)    = liftM snd $ projP v

projC :: (Value :<: v) => Term v Int -> Maybe Int
projC v = case project v of
            Just (Const n) -> return n; _ -> Nothing

projP :: (Value :<: v) => Term v (a,b) -> Maybe (Term v a, Term v b)
projP v = case project v of
            Just (Pair x y) -> return (x,y); _ -> Nothing

-- Example: evalMEx = Just (iConst 5)
evalMEx :: Maybe (Term Value Int)
evalMEx = evalM ((iConst 1) `iAdd`
                 (iConst 2 `iMult` iConst 2) :: Term Sig Int)