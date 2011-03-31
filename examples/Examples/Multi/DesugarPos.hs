{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs #-}
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
-- @FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@,
-- @GADTs@. Besides, GCH 7 is required.
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
          instanceHEqF, instanceHShowF, smartConstructors]
         [''Value, ''Op, ''Sugar])

-- Term homomorphism for desugaring of terms
class (HFunctor f, HFunctor g) => Desugar f g where
  desugHom :: TermHom f g
  desugHom = desugHom' . hfmap Hole
  desugHom' :: Alg f (Context g a)
  desugHom' x = appCxt (desugHom x)

instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
  desugHom (Inl x) = desugHom x
  desugHom (Inr x) = desugHom x
  desugHom' (Inl x) = desugHom' x
  desugHom' (Inr x) = desugHom' x

instance (Value :<: v, HFunctor v) => Desugar Value v where
  desugHom = simpCxt . inj

instance (Op :<: v, HFunctor v) => Desugar Op v where
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
desugP = appTermHom (productTermHom desugHom)

iSwapP :: (DistProd f p f', Sugar :<: f) => p -> Term f' (a,b) -> Term f' (b,a)
iSwapP p x = Term (injectP p $ inj $ Swap x)

iConstP :: (DistProd f p f', Value :<: f) => p -> Int -> Term f' Int
iConstP p x = Term (injectP p $ inj $ Const x)

iPairP :: (DistProd f p f', Value :<: f) => p -> Term f' a -> Term f' b -> Term f' (a,b)
iPairP p x y = Term (injectP p $ inj $ Pair x y)

iFstP :: (DistProd f p f', Op :<: f) => p -> Term f' (a,b) -> Term f' a
iFstP p x = Term (injectP p $ inj $ Fst x)

iSndP :: (DistProd f p f', Op :<: f) => p -> Term f' (a,b) -> Term f' b
iSndP p x = Term (injectP p $ inj $ Snd x)

-- Example: desugPEx = iPairP (Pos 1 0)
--                            (iSndP (Pos 1 0) (iPairP (Pos 1 1)
--                                                     (iConstP (Pos 1 2) 1)
--                                                     (iConstP (Pos 1 3) 2)))
--                            (iFstP (Pos 1 0) (iPairP (Pos 1 1)
--                                                     (iConstP (Pos 1 2) 1)
--                                                     (iConstP (Pos 1 3) 2)))
desugPEx :: Term SigP (Int,Int)
desugPEx = desugP $ iSwapP (Pos 1 0) (iPairP (Pos 1 1) (iConstP (Pos 1 2) 1)
                                                       (iConstP (Pos 1 3) 2))