{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Thunk
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This example illustrates how the ''Data.Comp.Thunk'' package can be
-- used to implement a non-strict language (or a partially non-strict
-- language).
--
--------------------------------------------------------------------------------

module Examples.Thunk where

import Data.Comp
import Data.Comp.Zippable
import Data.Comp.Thunk
import Data.Comp.Derive
import Data.Comp.Show()
import Control.Monad

-- Signature for values and operators
data Value e = Const Int | Pair e e
data Op e = Add e e | Mult e e | Fst e | Snd e

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [makeFunctor, makeTraversable, makeFoldable,
          makeEqF, makeShowF, smartConstructors]
         [''Value, ''Op])

instance Zippable Value where
    fzip (Cons x (Cons y _)) (Pair x' y') = Pair (x,x') (y,y')
    fzip _ (Const i) = Const i

-- Monadic term evaluation algebra
class EvalT f v where
  evalAlgT :: AlgT Maybe f v

$(derive [liftSum] [''EvalT])

type MTerm f = TermT Maybe f

-- Lift the monadic evaluation algebra to a monadic catamorphism
evalT :: (Traversable v, Functor f, EvalT f v) => Term f -> Maybe (Term v)
evalT = deepDethunk . cata evalAlgT

instance (Value :<: v) => EvalT Value v where
-- make pairs strict in both components
--  evalAlgT x@Pair{} = strict x
-- or explicitly:
--  evalAlgT (Pair x y) = thunk $ liftM2 iPair (dethunk' x) (dethunk' )y
--  evalAlgT x = inject x

-- or only partially strict
  evalAlgT = strictAt spec where
      spec (Pair _ b) = [b]
      spec _          = []

instance (Value :<: v) => EvalT Op v where
  evalAlgT (Add x y) = thunk $ do
                         n1 <- projC x
                         n2 <- projC y
                         return $ iConst $ n1 + n2
  evalAlgT (Mult x y) = thunk $ do
                          n1 <- projC x
                          n2 <- projC y
                          return $ iConst $ n1 * n2
  evalAlgT (Fst v)    = thunk $ liftM fst $ projP v
  evalAlgT (Snd v)    = thunk $ liftM snd $ projP v

projC :: (Value :<: v) => TermT Maybe v -> Maybe Int
projC v = do v' <- dethunk v
             case proj v' of
               Just (Const n) -> return n
               _ -> Nothing

projP :: (Value :<: v) => MTerm v -> Maybe (MTerm v, MTerm v)
projP v = do v' <- dethunk v
             case proj v' of
               Just (Pair x y) -> return (x,y)
               _ -> Nothing


evalTEx :: Maybe (Term Value)
evalTEx = evalT (iSnd (iFst (iConst 5) `iPair` iConst 4) :: Term Sig)