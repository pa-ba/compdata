{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs,
  KindSignatures, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.EvalM
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Monadic Expression Evaluation
--
-- The example illustrates how to use generalised parametric compositional data
-- types to implement a small expression language, with a language of values,
-- and a monadic evaluation function mapping expressions to values. The example
-- demonstrates how (parametric) abstractions are mapped to general functions,
-- from values to /monadic/ values, and how it is possible to project a general
-- value (with functions) back into ground values, that can again be analysed.
--
--------------------------------------------------------------------------------

module Examples.MultiParam.EvalM where

import Data.Comp.MultiParam
import Data.Comp.MultiParam.HDitraversable
import Data.Comp.MultiParam.Show ()
import Data.Comp.MultiParam.Derive
import Control.Monad ((<=<))

-- Signatures for values and operators
data Const :: (* -> *) -> (* -> *) -> * -> * where
    Const :: Int -> Const a e Int
data Lam :: (* -> *) -> (* -> *) -> * -> * where
    Lam :: (a i -> e j) -> Lam a e (i -> j)
data App :: (* -> *) -> (* -> *) -> * -> * where
    App :: e (i -> j) -> e i -> App a e j
data Op :: (* -> *) -> (* -> *) -> * -> * where
    Add :: e Int -> e Int -> Op a e Int
    Mult :: e Int -> e Int -> Op a e Int
data FunM :: (* -> *) -> (* -> *) -> (* -> *) -> * -> * where
    FunM :: (e i -> m (e j)) -> FunM m a e (i -> j)

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op
-- Signature for values. Note the use of 'FunM' rather than 'Lam' (!)
type Value = Const :+: FunM Maybe
-- Signature for ground values.
type GValue = Const

-- Derive boilerplate code using Template Haskell
$(derive [makeHDifunctor, makeEqHD, makeOrdHD, makeShowHD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op])

instance HDitraversable Const where
  hdimapM _ (Const n) = return $ Const n

-- Term evaluation algebra.
class EvalM f v where
  evalAlgM :: AlgM' Maybe f (Trm v a)

$(derive [liftSum] [''EvalM])

-- Lift the evaluation algebra to a catamorphism
evalM :: (HDifunctor f, EvalM f v) => Term f i -> Maybe (Term v i)
evalM t = termM (cataM' evalAlgM t)

instance (Const :<: v) => EvalM Const v where
  evalAlgM (Const n) = return $ iConst n

instance (Const :<: v) => EvalM Op v where
  evalAlgM (Add mx my) = do x <- projC =<< getCompose mx
                            y <- projC =<< getCompose my
                            return $ iConst $ x + y
  evalAlgM (Mult mx my) = do x <- projC =<< getCompose mx
                             y <- projC =<< getCompose my
                             return $ iConst $ x * y

instance (FunM Maybe :<: v) => EvalM App v where
  evalAlgM (App mx my) = do f <- projF =<< getCompose mx
                            f =<< getCompose my

instance (FunM Maybe :<: v) => EvalM Lam v where
  evalAlgM (Lam f) = return $ inject $ FunM $ getCompose . f

projC :: (Const :<: v) => Trm v a Int -> Maybe Int
projC v = case project v of
            Just (Const n) -> return n; _ -> Nothing

projF :: (FunM Maybe :<: v)
         => Trm v a (i -> j) -> Maybe (Trm v a i -> Maybe (Trm v a j))
projF v = case project v of
            Just (FunM f :: FunM Maybe a (Trm v a) (i -> j)) -> return f
            _ -> Nothing

-- |Evaluation of expressions to ground values.
evalMG :: Term Sig i -> Maybe (Term GValue i)
evalMG = deepProject <=< (evalM :: Term Sig i -> Maybe (Term Value i))

-- Example: evalEx = Just (iConst 12) (3 * (2 + 2) = 12)
evalMEx :: Maybe (Term GValue Int)
evalMEx = evalMG $ Term (iLam (\x -> iLam $ \y -> y `iMult` (x `iAdd` x))
                         `iApp` iConst 2 `iApp` iConst 3)