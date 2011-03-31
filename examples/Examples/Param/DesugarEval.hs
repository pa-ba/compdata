{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  TypeSynonymInstances #-}
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
-- @FlexibleInstances@, @FlexibleContexts@, @UndecidableInstances@, and
-- @TypeSynonymInstances@.
--
--------------------------------------------------------------------------------

module Examples.Param.DesugarEval where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Derive

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

-- Term homomorphism for desugaring of terms
class (Difunctor f, Difunctor g) => Desugar f g where
  desugHom :: TermHom f g
  desugHom = desugHom' . fmap Hole
  desugHom' :: (a :< b) => f a (Cxt g a b) -> Cxt g a b
  desugHom' x = appCxt (desugHom x)

desug :: (Desugar f g, Difunctor f) => Term f -> Term g
desug = appTermHom desugHom

instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
  desugHom (Inl x) = desugHom x
  desugHom (Inr x) = desugHom x
  desugHom' (Inl x) = desugHom' x
  desugHom' (Inr x) = desugHom' x

instance (Op :<: v, Difunctor v) => Desugar Op v where
  desugHom = simpCxt . inj

instance (Const :<: v, Difunctor v) => Desugar Const v where
  desugHom = simpCxt . inj

instance (Lam :<: v, Difunctor v) => Desugar Lam v where
  desugHom = simpCxt . inj

instance (App :<: v, Difunctor v) => Desugar App v where
  desugHom = simpCxt . inj

instance (IfThenElse :<: v, Difunctor v) => Desugar IfThenElse v where
  desugHom = simpCxt . inj

instance (Op :<: v, Const :<: v, Lam :<: v, App :<: v, Difunctor v)
  => Desugar Sug v where
  desugHom' (Neg x)   = iConst (-1) `iMult` x
  desugHom' (Let x y) = iLam y `iApp` x
  desugHom' Fix       = iLam $ \f ->
                           (iLam $ \x -> hole f `iApp` (hole x `iApp` hole x))
                           `iApp`
                           (iLam $ \x -> hole f `iApp` (hole x `iApp` hole x))
                               where hole = Hole . coerce

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

instance (Eval f v, Eval g v) => Eval (f :+: g) v where
  evalAlg (Inl x) = evalAlg x
  evalAlg (Inr x) = evalAlg x

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
evalEx = evalG $ iFix `iApp` fact `iApp` iConst 6

fact :: Term Sig'
fact = iLam $ \f ->
         iLam $ \n ->
             iIfThenElse
             (Hole n)
             ((Hole n) `iMult` (Hole f `iApp` (Hole n `iAdd` iConst (-1))))
             (iConst 1)