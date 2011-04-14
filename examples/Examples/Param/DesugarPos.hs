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
-- Desugaring + Propagation of Annotations.
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
$(derive [instanceDifunctor, instanceEqD, instanceShowD,
          smartConstructors, smartAConstructors]
         [''Const, ''Lam, ''App, ''Op, ''Sug])

instance (Op :<: f, Const :<: f, Lam :<: f, App :<: f, Difunctor f)
  => Desugar Sug f where
  desugHom' (Neg x)   = iConst (-1) `iMult` x
  desugHom' (Let x y) = iLam y `iApp` x
  desugHom' Fix       = iLam $ \f ->
                           (iLam $ \x -> Place f `iApp` (Place x `iApp` Place x))
                           `iApp`
                           (iLam $ \x -> Place f `iApp` (Place x `iApp` Place x))

-- Example: desugPEx == iAApp (Pos 1 0)
--          (iALam (Pos 1 0) Place)
--          (iALam (Pos 1 1) $ \f ->
--               iAApp (Pos 1 1)
--                     (iALam (Pos 1 1) $ \x ->
--                          iAApp (Pos 1 1) (Place f) (iAApp (Pos 1 1) (Place x) (Place x)))
--                     (iALam (Pos 1 1) $ \x ->
--                          iAApp (Pos 1 1) (Place f) (iAApp (Pos 1 1) (Place x) (Place x))))
desugPEx :: Term SigP
desugPEx = desugarA (iALet (Pos 1 0) (iAFix (Pos 1 1)) Place :: Term SigP')