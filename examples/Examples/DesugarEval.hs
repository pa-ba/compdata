{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.DesugarEval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Desugaring + Expression Evaluation
--
-- The example illustrates how to compose a term homomorphism and an algebra,
-- exemplified via a desugaring term homomorphism and an evaluation algebra.
--
--------------------------------------------------------------------------------

module Examples.DesugarEval where

import Data.Comp
import Data.Comp.Show ()
import Data.Comp.Derive
import Data.Comp.Desugar

-- Signature for values, operators, and syntactic sugar
data Value e = Const Int | Pair e e
data Op e = Add e e | Mult e e | Fst e | Snd e
data Sugar e = Neg e | Swap e

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sugar :+: Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [makeFunctor, makeTraversable, makeFoldable,
          makeEqF, makeShowF, makeOrdF, smartConstructors]
         [''Value, ''Op, ''Sugar])

instance (Op :<: f, Value :<: f, Functor f) => Desugar Sugar f where
  desugHom' (Neg x)  = iConst (-1) `iMult` x
  desugHom' (Swap x) = iSnd x `iPair` iFst x

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

$(derive [liftSum] [''Eval])

instance (Value :<: v) => Eval Value v where
  evalAlg = inject

instance (Value :<: v) => Eval Op v where
  evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
  evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
  evalAlg (Fst x)    = fst $ projP x
  evalAlg (Snd x)    = snd $ projP x

projC :: (Value :<: v) => Term v -> Int
projC v = case project v of Just (Const n) -> n

projP :: (Value :<: v) => Term v -> (Term v, Term v)
projP v = case project v of Just (Pair x y) -> (x,y)

-- Compose the evaluation algebra and the desugaring homomorphism to an algebra
eval :: Term Sig -> Term Value
eval = cata evalAlg

evalDesug :: Term Sig' -> Term Value
evalDesug = eval . desugar

-- Example: evalEx = iPair (iConst 2) (iConst 1)
evalEx :: Term Value
evalEx = evalDesug $ iSwap $ iPair (iConst 1) (iConst 2)