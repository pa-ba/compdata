{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Lambda
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lambda calculus examples
--
-- Parallel reduction and CPS translation for lambda calculus. The examples are
-- taken from Washburn and Weirich (Journal of Functional Programming, 2008
-- vol. 18 (01) pp. 87-140, http://dx.doi.org/10.1017/S0956796807006557).
--
--
--------------------------------------------------------------------------------

module Examples.Param.Lambda where

import Data.Comp.Param
import Data.Comp.Param.Show ()
import Data.Comp.Param.Derive

-- Signatures for the lambda calculus
data Lam a e = Lam (a -> e) -- Note: not e -> e
data App a e = App e e
type Sig     = Lam :+: App

-- Derive boilerplate code using Template Haskell
$(derive [makeDifunctor, makeDitraversable, makeEqD, makeOrdD, makeShowD,
          smartConstructors] [''Lam, ''App])

--------------------------------------------------------------------------------
-- Parallel reduction
--------------------------------------------------------------------------------

data Par f a = Par{par :: Trm f a, apply :: Trm f a -> Trm f a}

class ParRed f v where
  parRedAlg :: Alg f (Par v a)

$(derive [liftSum] [''ParRed])

parRed :: (Difunctor f, ParRed f v) => Term f -> Term v
parRed t = Term $ par $ cata parRedAlg t

instance (App :<: v) => ParRed App v where
  parRedAlg (App x y) = Par{par = apply x (par y),
                            apply = iApp (apply x (par y))}

instance (Lam :<: v, App :<: v) => ParRed Lam v where
  parRedAlg (Lam f) = Par{par = iLam (par . f . var),
                          apply = par . f . var}
      where var :: (App :<: f) => Trm f a -> Par f a
            var x = Par{par = x, apply = iApp x}

e :: Term Sig
e = Term $ iApp (iLam (\x -> iApp x x)) (iLam (\y -> y))

e' :: Term Sig
e' = parRed e


--------------------------------------------------------------------------------
-- CPS translation
--------------------------------------------------------------------------------

data CPS f a = CPS{cpsmeta :: (Trm f a -> Trm f a) -> Trm f a,
                   cpsobj :: Trm f a -> Trm f a}

class CPSTrans f v where
  cpsTransAlg :: Alg f (CPS v a)

$(derive [liftSum] [''CPSTrans])

cpsTrans :: (Difunctor f, CPSTrans f v, Lam :<: v, App :<: v) => Term f -> Term v
cpsTrans t = Term $ iLam (\a -> cpsmeta (cata cpsTransAlg t) (\m -> iApp a m))

instance (App :<: v, Lam :<: v) => CPSTrans App v where
  cpsTransAlg (App x y) = CPS{cpsmeta = \k -> appexp (iLam k),
                              cpsobj = appexp}
    where appexp c = cpsmeta x (\y1 -> cpsmeta y (\y2 -> iApp (iApp y1 y2) c))

instance (Lam :<: v, App :<: v) => CPSTrans Lam v where
  cpsTransAlg (Lam f) = value (iLam (iLam . cpsobj . f . value))
    where value x = CPS{cpsmeta = \k -> k x, cpsobj = \c -> iApp c x}

e1 :: Term Sig
e1 = Term $ iLam (\x -> iApp x x)

e1' :: Term Sig
e1' = cpsTrans e1