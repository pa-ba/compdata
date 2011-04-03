{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
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
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.
--
--------------------------------------------------------------------------------

module Examples.DesugarEval where

import Data.Comp
import Data.Comp.Show ()
import Data.Comp.Derive

-- Signature for values, operators, and syntactic sugar
data Value e = Const Int | Pair e e
data Op e = Add e e | Mult e e | Fst e | Snd e
data Sugar e = Neg e | Swap e

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sugar :+: Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [instanceFunctor, instanceTraversable, instanceFoldable,
          instanceEqF, instanceShowF, smartConstructors]
         [''Value, ''Op, ''Sugar])

-- Term homomorphism for desugaring of terms
class (Functor f, Functor g) => Desugar f g where
  desugHom :: TermHom f g
  desugHom = desugHom' . fmap Hole
  desugHom' :: Alg f (Context g a)
  desugHom' x = appCxt (desugHom x)

instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
  desugHom (Inl x) = desugHom x
  desugHom (Inr x) = desugHom x
  desugHom' (Inl x) = desugHom' x
  desugHom' (Inr x) = desugHom' x

instance (Value :<: f, Functor f) => Desugar Value f where
  desugHom = simpCxt . inj

instance (Op :<: f, Functor f) => Desugar Op f where
  desugHom = simpCxt . inj

instance (Op :<: f, Value :<: f, Functor f) => Desugar Sugar f where
  desugHom' (Neg x)  = iConst (-1) `iMult` x
  desugHom' (Swap x) = iSnd x `iPair` iFst x

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

instance (Eval f v, Eval g v) => Eval (f :+: g) v where
  evalAlg (Inl x) = evalAlg x
  evalAlg (Inr x) = evalAlg x

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
eval :: Term Sig' -> Term Value
eval = cata (evalAlg `compAlg` (desugHom :: TermHom Sig' Sig))

-- Example: evalEx = iPair (iConst 2) (iConst 1)
evalEx :: Term Value
evalEx = eval $ iSwap $ iPair (iConst 1) (iConst 2)