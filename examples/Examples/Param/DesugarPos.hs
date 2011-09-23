{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  TypeSynonymInstances, OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.DesugarPos
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Desugaring + Propagation of Annotations
--
-- The example illustrates how to compose a term homomorphism and an algebra,
-- exemplified via a desugaring term homomorphism and an evaluation algebra.
--
--------------------------------------------------------------------------------

module Examples.Param.DesugarPos where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Show ()
import Data.Comp.Param.Derive
import Data.Comp.Param.Desugar

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
$(derive [makeDifunctor, makeEqD, makeOrdD, makeShowD,
          smartConstructors, smartAConstructors]
         [''Const, ''Lam, ''App, ''Op, ''Sug])

instance (Op :<: f, Const :<: f, Lam :<: f, App :<: f, Difunctor f)
  => Desugar Sug f where
  desugHom' (Neg x)   = iConst (-1) `iMult` x
  desugHom' (Let x y) = inject (Lam y) `iApp` x
  desugHom' Fix       = iLam $ \f -> iLam (\x -> f `iApp` (x `iApp` x)) `iApp`
                                     iLam (\x -> f `iApp` (x `iApp` x))

-- Example: desugPEx == iAApp (Pos 1 0)
--          (iALam (Pos 1 0) id)
--          (iALam (Pos 1 1) $ \f ->
--               iAApp (Pos 1 1)
--                     (iALam (Pos 1 1) $ \x ->
--                          iAApp (Pos 1 1) f (iAApp (Pos 1 1) x x))
--                     (iALam (Pos 1 1) $ \x ->
--                          iAApp (Pos 1 1) f (iAApp (Pos 1 1) x  x)))
desugPEx :: Term SigP
desugPEx = desugarA (iALet (Pos 1 0) (iAFix (Pos 1 1)) id :: Term SigP')