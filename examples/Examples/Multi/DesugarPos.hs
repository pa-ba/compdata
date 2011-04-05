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
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, @UndecidableInstances@,
-- @GADTs@, and @OverlappingInstances@. Besides, GCH 7 is required.
--
--------------------------------------------------------------------------------

module Examples.Multi.DesugarPos where

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Derive

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

-- Term homomorphism for desugaring of terms
class (HFunctor f, HFunctor g) => Desugar f g where
  desugHom :: TermHom f g
  desugHom = desugHom' . hfmap Hole
  desugHom' :: Alg f (Context g a)
  desugHom' x = appCxt (desugHom x)

$(derive [liftSum] [''Desugar])

-- Default desugaring implementation
instance (HFunctor f, HFunctor g, f :<: g) => Desugar f g where
  desugHom = simpCxt . inj

instance (Op :<: v, Value :<: v, HFunctor v) => Desugar Sugar v where
  desugHom' (Neg x)  = iConst (-1) `iMult` x
  desugHom' (Swap x) = iSnd x `iPair` iFst x

-- Lift the desugaring term homomorphism to a catamorphism
desug :: Term Sig' :-> Term Sig
desug = appTermHom desugHom

-- Example: desugEx = iPair (iConst 2) (iConst 1)
desugEx :: Term Sig (Int,Int)
desugEx = desug $ iSwap $ iPair (iConst 1) (iConst 2)

-- Lift desugaring to terms annotated with source positions
desugP :: Term SigP' :-> Term SigP
desugP = appTermHom (propAnn desugHom)

-- Example: desugPEx = iAPair (Pos 1 0)
--                            (iASnd (Pos 1 0) (iAPair (Pos 1 1)
--                                                     (iAConst (Pos 1 2) 1)
--                                                     (iAConst (Pos 1 3) 2)))
--                            (iAFst (Pos 1 0) (iAPair (Pos 1 1)
--                                                     (iAConst (Pos 1 2) 1)
--                                                     (iAConst (Pos 1 3) 2)))
desugPEx :: Term SigP (Int,Int)
desugPEx = desugP $ iASwap (Pos 1 0) (iAPair (Pos 1 1) (iAConst (Pos 1 2) 1)
                                                       (iAConst (Pos 1 3) 2))