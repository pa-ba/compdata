{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs,
  OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Multi.DesugarPos
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Desugaring + Propagation of Annotations
--
-- The example illustrates how to lift a term homomorphism to products,
-- exemplified via a desugaring term homomorphism lifted to terms annotated with
-- source position information.
--
--------------------------------------------------------------------------------

module Examples.Multi.DesugarPos where

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Desugar

-- Signature for values, operators, and syntactic sugar
data Value e l where
  Const  ::        Int -> Value e Int
  Pair   :: e s -> e t -> Value e (s,t)
data Op e l where
  Add, Mult  :: e Int -> e Int   -> Op e Int
  Fst        ::          e (s,t) -> Op e s
  Snd        ::          e (s,t) -> Op e t
data Sugar e l where
  Neg   :: e Int   -> Sugar e Int
  Swap  :: e (s,t) -> Sugar e (t,s)

-- Source position information (line number, column number)
data Pos = Pos Int Int
           deriving (Show, Eq)

-- Signature for the simple expression language
type Sig = Op :+: Value
type SigP = Op :&: Pos :+: Value :&: Pos

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sugar :+: Op :+: Value
type SigP' = Sugar :&: Pos :+: Op :&: Pos :+: Value :&: Pos

-- Derive boilerplate code using Template Haskell (GHC 7 needed)
$(derive [instanceHFunctor, instanceHTraversable, instanceHFoldable,
          instanceHEqF, instanceHShowF, smartConstructors, smartAConstructors]
         [''Value, ''Op, ''Sugar])

instance (Op :<: v, Value :<: v, HFunctor v) => Desugar Sugar v where
  desugHom' (Neg x)  = iConst (-1) `iMult` x
  desugHom' (Swap x) = iSnd x `iPair` iFst x

-- Example: desugEx = iPair (iConst 2) (iConst 1)
desugEx :: Term Sig (Int,Int)
desugEx = desugar (iSwap $ iPair (iConst 1) (iConst 2) :: Term Sig' (Int,Int))

-- Example: desugPEx = iAPair (Pos 1 0)
--                            (iASnd (Pos 1 0) (iAPair (Pos 1 1)
--                                                     (iAConst (Pos 1 2) 1)
--                                                     (iAConst (Pos 1 3) 2)))
--                            (iAFst (Pos 1 0) (iAPair (Pos 1 1)
--                                                     (iAConst (Pos 1 2) 1)
--                                                     (iAConst (Pos 1 3) 2)))
desugPEx :: Term SigP (Int,Int)
desugPEx = desugarA (iASwap (Pos 1 0) (iAPair (Pos 1 1) (iAConst (Pos 1 2) 1)
                                                        (iAConst (Pos 1 3) 2))
                     :: Term SigP' (Int,Int))