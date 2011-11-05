{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs,
  OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Multi.Desugar
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
-- The example also illustrates how to lift a term homomorphism to products,
-- exemplified via a desugaring term homomorphism lifted to terms annotated with
-- source position information.
--
--------------------------------------------------------------------------------

module Examples.Multi.Desugar where

import Data.Comp.Multi
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Desugar
import Examples.Multi.Common
import Examples.Multi.Eval

-- Signature for syntactic sugar
data Sugar a i where
  Neg  :: a Int   -> Sugar a Int
  Swap :: a (i,j) -> Sugar a (j,i)

-- Source position information (line number, column number)
data Pos = Pos Int Int
           deriving (Eq, Show)

-- Signature for the simple expression language
type SigP = Op :&: Pos :+: Value :&: Pos

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sugar :+: Op :+: Value
type SigP' = Sugar :&: Pos :+: Op :&: Pos :+: Value :&: Pos

-- Derive boilerplate code using Template Haskell (GHC 7 needed)
$(derive [makeHFunctor, makeHTraversable, makeHFoldable, makeEqHF, makeShowHF,
          makeOrdHF, smartConstructors, smartAConstructors]
         [''Sugar])

instance (Op :<: v, Value :<: v, HFunctor v) => Desugar Sugar v where
  desugHom' (Neg x)  = iConst (-1) `iMult` x
  desugHom' (Swap x) = iSnd x `iPair` iFst x

-- Compose the evaluation algebra and the desugaring homomorphism to an
-- algebra
evalDesug :: Term Sig' :-> Term Value
evalDesug = cata (evalAlg `compAlg` (desugHom :: Hom Sig' Sig))

-- Example: evalEx = iPair (iConst 2) (iConst 1)
evalEx :: Term Value (Int,Int)
evalEx = evalDesug $ iSwap $ iPair (iConst 1) (iConst 2)

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