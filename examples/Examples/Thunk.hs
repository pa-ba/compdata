{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, OverlappingInstances #-}
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
import Data.Comp.Thunk
import Data.Comp.Derive
import Data.Comp.Show()
import Control.Monad
import Examples.Common hiding (Value(..), Sig)

-- Signature for values, strict pairs
data Value a = Const Int | Pair !a !a

-- Signature for the simple expression language
type Sig = Op :+: Value

-- Derive boilerplate code using Template Haskell
$(derive [makeFunctor, makeTraversable, makeFoldable,
          makeEqF, makeShowF, smartConstructors, makeHaskellStrict]
         [''Value])

-- Monadic term evaluation algebra
class EvalT f v where
  evalAlgT :: Monad m => AlgT m f v

$(derive [liftSum] [''EvalT])

-- Lift the monadic evaluation algebra to a monadic catamorphism
evalT :: (Traversable v, Functor f, EvalT f v, Monad m) => Term f -> m (Term v)
evalT = nf . cata evalAlgT

instance (Value :<: v) => EvalT Value v where
-- make pairs strict in both components
--  evalAlgT x@Pair{} = strict x
-- or explicitly:
--  evalAlgT (Pair x y) = thunk $ liftM2 iPair (dethunk' x) (dethunk' )y
--  evalAlgT x = inject x

-- or only partially strict
  evalAlgT = haskellStrict'

instance (Value :<: v) => EvalT Op v where
  evalAlgT (Add x y) = thunk $ do
                         Const n1 <- whnfPr x
                         Const n2 <- whnfPr y
                         return $ iConst $ n1 + n2
  evalAlgT (Mult x y) = thunk $ do
                          Const n1 <- whnfPr x
                          Const n2 <- whnfPr y
                          return $ iConst $ n1 * n2
  evalAlgT (Fst v)    = thunk $ do 
                          Pair x _  <- whnfPr v
                          return x
  evalAlgT (Snd v)    = thunk $ do 
                          Pair _ y <- whnfPr v
                          return y


{-instance Monad (Either String) where
    Left msg >>= _ = Left msg
    Right x >>= f = f x
                      
    return = Right
    fail = Left-}

evalTEx :: Either String (Term Value)
evalTEx = evalT (iSnd (iFst (iConst 5) `iPair` iConst 4) :: Term Sig)