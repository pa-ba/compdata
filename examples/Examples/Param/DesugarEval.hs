{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  TypeSynonymInstances, OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.DesugarEval
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
-- The example extends the example from 'Examples.Param.Eval'.
--
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, @UndecidableInstances@,
-- @TypeSynonymInstances@, and @OverlappingInstances@.
--
--------------------------------------------------------------------------------

module Examples.Param.DesugarEval where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Show ()
import Data.Comp.Param.Derive
import Data.Comp.Param.Desugar

-- Signatures for values and operators
data Const a e = Const Int
data Lam a e = Lam (a -> e) -- Note: not e -> e
data App a e = App e e
data Op a e = Add e e | Mult e e
data Fun a e = Fun (e -> e) -- Note: not a -> e
data IfThenElse a e = IfThenElse e e e

-- Signature for syntactic sugar (negation, let expressions, Y combinator)
data Sug a e = Neg e | Let e (a -> e) | Fix

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op :+: IfThenElse
-- Signature for the simple expression language with syntactic sugar
type Sig' = Sug :+: Sig
-- Signature for values. Note the use of 'Fun' rather than 'Lam' (!)
type Value = Const :+: Fun
-- Signature for ground values.
type GValue = Const

-- Derive boilerplate code using Template Haskell
$(derive [instanceDifunctor, instanceEqD, instanceShowD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op, ''IfThenElse, ''Sug])
$(derive [instanceFoldable, instanceTraversable]
         [''Const, ''App, ''Op])
$(derive [smartConstructors] [''Fun])

instance (Op :<: f, Const :<: f, Lam :<: f, App :<: f, Difunctor f)
  => Desugar Sug f where
  desugHom' (Neg x)   = iConst (-1) `iMult` x
  desugHom' (Let x y) = iLam y `iApp` x
  desugHom' Fix       = iLam $ \f ->
                           (iLam $ \x -> Place f `iApp` (Place x `iApp` Place x))
                           `iApp`
                           (iLam $ \x -> Place f `iApp` (Place x `iApp` Place x))

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

$(derive [liftSum] [''Eval])

-- Compose the evaluation algebra and the desugaring homomorphism to an algebra
eval :: Term Sig' -> Term Value
eval = cata (evalAlg `compAlg` (desugHom :: TermHom Sig' Sig))

instance (Const :<: v) => Eval Const v where
  evalAlg (Const n) = iConst n

instance (Const :<: v) => Eval Op v where
  evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
  evalAlg (Mult x y) = iConst $ (projC x) * (projC y)

instance (Fun :<: v) => Eval App v where
  evalAlg (App x y) = (projF x) y

instance (Fun :<: v) => Eval Lam v where
  evalAlg (Lam f) = iFun f

instance (Const :<: v) => Eval IfThenElse v where
  evalAlg (IfThenElse c v1 v2) = if projC c /= 0 then v1 else v2

projC :: (Const :<: v) => Term v -> Int
projC v = case project v of Just (Const n) -> n

projF :: (Fun :<: v) => Term v -> Term v -> Term v
projF v = case project v of Just (Fun f) -> f

-- |Evaluation of expressions to ground values.
evalG :: Term Sig' -> Maybe (Term GValue)
evalG = deepProject' . (eval :: Term Sig' -> Term Value)

-- Example: evalEx = Just (iConst 720)
evalEx :: Maybe (Term GValue)
evalEx = evalG $ fact `iApp` iConst 6

fact :: Term Sig'
fact = iFix `iApp`
       (iLam $ \f ->
          iLam $ \n ->
              iIfThenElse
              (Place n)
              (Place n `iMult` (Place f `iApp` (Place n `iAdd` iConst (-1))))
              (iConst 1))