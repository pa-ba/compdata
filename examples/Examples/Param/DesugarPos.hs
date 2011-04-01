{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  TypeSynonymInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.DesugarPos
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Desugaring + Propagation of Annotations.
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

module Examples.Param.DesugarPos where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Derive

-- Signatures for values and operators
data Const a e = Const Int
data Lam a e = Lam (a -> e) -- Note: not e -> e
data App a e = App e e
data Op a e = Add e e | Mult e e

-- Signature for syntactic sugar (negation, let expressions, Y combinator)
data Sug a e = Neg e | Let e (a -> e) | Fix

-- Source position information (line number, column number)
data Pos = Pos Int Int
           deriving (Show, Eq)

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op
type SigP = Const :&: Pos :+: Lam :&: Pos :+: App :&: Pos :+: Op :&: Pos

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sug :+: Sug
type SigP' = Sug :&: Pos :+: SigP

-- Derive boilerplate code using Template Haskell
$(derive [instanceDifunctor, instanceEqD, instanceShowD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op, ''Sug])
-- $(derive [instanceFoldable, instanceTraversable]
--          [''Const, ''App, ''Op])
-- $(derive [smartConstructors] [''Fun])

-- Term homomorphism for desugaring of terms
class (Difunctor f, Difunctor g) => Desugar f g where
  desugHom :: TermHom f g
  desugHom = desugHom' . fmap Hole
  desugHom' :: (a :< b) => f a (Cxt g a b) -> Cxt g a b
  desugHom' x = appCxt (desugHom x)

desug :: (Desugar f g, Difunctor f) => Term f -> Term g
desug = appTermHom desugHom

-- Lift desugaring to terms annotated with source positions
desugP :: Term SigP' -> Term SigP
desugP = appTermHom (productTermHom desugHom)

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

instance (Op :<: v, Const :<: v, Lam :<: v, App :<: v, Difunctor v)
  => Desugar Sug v where
  desugHom' (Neg x)   = iConst (-1) `iMult` x
  desugHom' (Let x y) = iLam y `iApp` x
  desugHom' Fix       = iLam $ \f ->
                           (iLam $ \x -> hole f `iApp` (hole x `iApp` hole x))
                           `iApp`
                           (iLam $ \x -> hole f `iApp` (hole x `iApp` hole x))
                               where hole = Hole . coerce

iLamP :: (DistProd f p f', Lam :<: f) => p -> (a -> Cxt f' a b) -> Cxt f' a b
iLamP p x = Term (injectP p $ inj $ Lam x)

iLetP p a b = Term (injectP p $ inj $ Let a b)

iFixP p = Term (injectP p $ inj Fix)

desugPEx :: Term SigP
desugPEx = desugP $ iLetP (Pos 1 0) (iFixP (Pos 1 1)) Hole