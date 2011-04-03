{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.DesugarPos
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Desugaring + Propagation of Annotations.
--
-- The example illustrates how to lift a term homomorphism to products,
-- exemplified via a desugaring term homomorphism lifted to terms annotated with
-- source position information.
--
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.
--
--------------------------------------------------------------------------------

module Examples.DesugarPos where

import Data.Comp
import Data.Comp.Show ()
import Data.Comp.Equality ()
import Data.Comp.Derive

-- Signature for values, operators, and syntactic sugar
data Value e = Const Int | Pair e e
data Op e = Add e e | Mult e e | Fst e | Snd e
data Sugar e = Neg e | Swap e

-- Source position information (line number, column number)
data Pos = Pos Int Int
           deriving (Show, Eq)

-- Signature for the simple expression language
type Sig = Op :+: Value
type SigP = Op :&: Pos :+: Value :&: Pos

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sugar :+: Op :+: Value
type SigP' = Sugar :&: Pos :+: Op :&: Pos :+: Value :&: Pos

-- Derive boilerplate code using Template Haskell
$(derive [instanceFunctor, instanceTraversable, instanceFoldable,
          instanceEqF, instanceShowF, smartConstructors, smartPConstructors]
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

-- Lift the desugaring term homomorphism to a catamorphism
desug :: Term Sig' -> Term Sig
desug = appTermHom desugHom

-- Example: desugEx = iPair (iConst 2) (iConst 1)
desugEx :: Term Sig
desugEx = desug $ iSwap $ iPair (iConst 1) (iConst 2)

-- Lift desugaring to terms annotated with source positions
desugP :: Term SigP' -> Term SigP
desugP = appTermHom (productTermHom desugHom)

-- Example: desugPEx = iPPair (Pos 1 0)
--                            (iPSnd (Pos 1 0) (iPPair (Pos 1 1)
--                                                     (iPConst (Pos 1 2) 1)
--                                                     (iPConst (Pos 1 3) 2)))
--                            (iPFst (Pos 1 0) (iPPair (Pos 1 1)
--                                                     (iPConst (Pos 1 2) 1)
--                                                     (iPConst (Pos 1 3) 2)))
desugPEx :: Term SigP
desugPEx = desugP $ iPSwap (Pos 1 0) (iPPair (Pos 1 1) (iPConst (Pos 1 2) 1)
                                                       (iPConst (Pos 1 3) 2))