{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.EvalM
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Expression Evaluation
--
-- The example illustrates how to use parametric compositional data types to
-- implement a small expression language, with a language of values, and
-- a monadic evaluation function mapping expressions to values. The example
-- demonstrates how (parametric) abstractions are mapped to general functions,
-- from values to /monadic/ values, and how it is possible to project a general
-- value (with functions) back into ground values, that can again be analysed.
--
-- The example lifts the example from 'Examples.Param.Eval' to monadic
-- evaluation.
--
-- The following language extensions are needed in order to run the example:
-- @TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
-- @FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.
--
--------------------------------------------------------------------------------

module Examples.Param.EvalM where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Show ()
import Data.Comp.Param.Derive
import Control.Monad ((<=<))

-- Signatures for values and operators
data Const a e = Const Int
data Lam a e = Lam (a -> e) -- Note: not e -> e
data App a e = App e e
data Op a e = Add e e | Mult e e
data FunM m a e = FunM (e -> m e) -- Note: not a -> m e

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op
-- Signature for values. Note the use of 'FunM' rather than 'Lam' (!)
type Value = Const :+: FunM Maybe
-- Signature for ground values.
type GValue = Const

-- Derive boilerplate code using Template Haskell
$(derive [instanceDifunctor, instanceEqD, instanceShowD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op])
$(derive [instanceFoldable, instanceTraversable]
         [''Const, ''App, ''Op])
$(derive [smartConstructors] [''FunM])

-- Term evaluation algebra. Note that we cannot use @AlgM Maybe f (Term v)@
-- because that would force @FunM@ to have the type @e -> e@ rather than
-- @e -> m e@. The latter is needed because the input to a @Lam@ (which is
-- evaluated to a @Fun@) will determine whether or not an error should be
-- returned. Example: @(\x -> x x) 42@ will produce an error because the
-- abstraction is applied to a non-functional, whereas @(\x -> x x)(\y -> y)@
-- will not.
class EvalM f v where
  evalAlgM :: Alg f (Maybe (Term v))

$(derive [liftSum] [''EvalM])

-- Lift the evaluation algebra to a catamorphism
evalM :: (Difunctor f, EvalM f v) => Term f -> Maybe (Term v)
evalM = cata evalAlgM

instance (Const :<: v) => EvalM Const v where
  evalAlgM (Const n) = return $ iConst n

instance (Const :<: v) => EvalM Op v where
  evalAlgM (Add mx my)  = do x <- projC =<< mx
                             y <- projC =<< my
                             return $ iConst $ x + y
  evalAlgM (Mult mx my) = do x <- projC =<< mx
                             y <- projC =<< my
                             return $ iConst $ x * y

instance (FunM Maybe :<: v) => EvalM App v where
  evalAlgM (App mx my) = do f <- projF =<< mx
                            f =<< my

instance (FunM Maybe :<: v) => EvalM Lam v where
  evalAlgM (Lam f) = return $ iFunM $ f . return

projC :: (Const :<: v) => Term v -> Maybe Int
projC v = do Const n <- project v
             return n

projF :: (FunM Maybe :<: v) => Term v -> Maybe (Term v -> Maybe (Term v))
projF v = do FunM f <- project v
             return f

-- |Evaluation of expressions to ground values.
evalMG :: Term Sig -> Maybe (Term GValue)
evalMG = deepProject' <=< (evalM :: Term Sig -> Maybe (Term Value))

-- Example: evalEx = Just (iConst 12) (3 * (2 + 2) = 12)
evalMEx :: Maybe (Term GValue)
evalMEx = evalMG $ (iLam $ \x -> iLam $ \y ->
                                 Place y `iMult` (Place x `iAdd` Place x))
                   `iApp` iConst 2 `iApp` iConst 3