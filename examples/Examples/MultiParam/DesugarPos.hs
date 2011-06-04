{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  TypeSynonymInstances, OverlappingInstances, GADTs, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.DesugarPos
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
--------------------------------------------------------------------------------

module Examples.MultiParam.DesugarPos where

import Data.Comp.MultiParam hiding (Const)
import Data.Comp.MultiParam.Show ()
import Data.Comp.MultiParam.Derive
import Data.Comp.MultiParam.Desugar

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
data Fun :: (* -> *) -> (* -> *) -> * -> * where
    Fun :: (e i -> e j) -> Fun a e (i -> j)
data IfThenElse :: (* -> *) -> (* -> *) -> * -> * where
                   IfThenElse :: (e Int) -> (e i) -> (e i) -> IfThenElse a e i

-- Signature for syntactic sugar (negation, let expressions)
data Sug :: (* -> *) -> (* -> *) -> * -> * where
            Neg :: e Int -> Sug a e Int
            Let :: e i -> (a i -> e j) -> Sug a e j

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
$(derive [makeHDifunctor, makeEqHD, makeShowHD,
          smartConstructors, smartAConstructors]
         [''Const, ''Lam, ''App, ''Op, ''Sug])

instance (Op :<: f, Const :<: f, Lam :<: f, App :<: f, HDifunctor f)
  => Desugar Sug f where
  desugHom' (Neg x)   = iConst (-1) `iMult` x
  desugHom' (Let x y) = iLam y `iApp` x

-- Example: desugPEx == iAApp (Pos 1 0)
-- (iALam (Pos 1 0) $ \x -> iAMult (Pos 1 2) (iAConst (Pos 1 2) (-1)) (Place x))
-- (iAConst (Pos 1 1) 6)
desugPEx :: Term SigP Int
desugPEx = desugarA (iALet (Pos 1 0)
                           (iAConst (Pos 1 1) 6)
                           (\x -> iANeg (Pos 1 2) $ Place x :: Term SigP' Int))