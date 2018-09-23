{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Desugar
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Desugaring
--
-- The example illustrates how to compose a term homomorphism and an algebra,
-- exemplified via a desugaring term homomorphism and an evaluation algebra.
-- The example also illustrates how to lift a term homomorphism to annotations,
-- exemplified via a desugaring term homomorphism lifted to terms annotated with
-- source position information.
--
--------------------------------------------------------------------------------

module Examples.Desugar where

import Data.Comp
import Data.Comp.Show ()
import Data.Comp.Derive
import Data.Comp.Desugar
import Examples.Common
import Examples.Eval

-- Signature for syntactic sugar
data Sugar a = Neg a | Swap a
  deriving Functor

-- Source position information (line number, column number)
data Pos = Pos Int Int
           deriving (Show, Eq)

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sugar :+: Op :+: Value

-- Signature for the simple expression language with annotations
type SigP = Op :&: Pos :+: Value :&: Pos

-- Signature for the simple expression language, extended with syntactic sugar,
-- with annotations
type SigP' = Sugar :&: Pos :+: Op :&: Pos :+: Value :&: Pos

-- Derive boilerplate code using Template Haskell
$(derive [makeTraversable, makeFoldable,
          makeEqF, makeShowF, makeOrdF, smartConstructors, smartAConstructors]
         [''Sugar])

instance (Op :<: f, Value :<: f, Functor f) => Desugar Sugar f where
  desugHom' (Neg x)  = iConst (-1) `iMult` x
  desugHom' (Swap x) = iSnd x `iPair` iFst x

evalDesug :: Term Sig' -> Term Value
evalDesug = eval . (desugar :: Term Sig' -> Term Sig)

-- Example: evalEx = iPair (iConst 2) (iConst 1)
evalEx :: Term Value
evalEx = evalDesug $ iSwap $ iPair (iConst 1) (iConst 2)

-- Lift desugaring to terms annotated with source positions
desugP :: Term SigP' -> Term SigP
desugP = appHom (propAnn desugHom)

-- Example: desugPEx = iAPair (Pos 1 0)
--                            (iASnd (Pos 1 0) (iAPair (Pos 1 1)
--                                                     (iAConst (Pos 1 2) 1)
--                                                     (iAConst (Pos 1 3) 2)))
--                            (iAFst (Pos 1 0) (iAPair (Pos 1 1)
--                                                     (iAConst (Pos 1 2) 1)
--                                                     (iAConst (Pos 1 3) 2)))
desugPEx :: Term SigP
desugPEx = desugP $ iASwap (Pos 1 0) (iAPair (Pos 1 1) (iAConst (Pos 1 2) 1)
                                                       (iAConst (Pos 1 3) 2))
