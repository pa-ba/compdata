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

import Data.Comp.Param hiding (Const)
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

data Par f = Par{par :: Term f, apply :: Term f -> Term f}

class ParRed f v where
  parRedAlg :: Alg f (Par v)

$(derive [liftSum] [''ParRed])

parRed :: (Difunctor f, ParRed f v) => Term f -> Term v
parRed = par . cata parRedAlg

instance (App :<: v) => ParRed App v where
  parRedAlg (App x y) = Par{par = apply x (par y),
                            apply = iApp (apply x (par y))}

instance (Lam :<: v, App :<: v) => ParRed Lam v where
  parRedAlg (Lam f) = Par{par = iLam (par . f . var),
                          apply = par . f . var}
      where var :: (App :<: f) => Term f -> Par f
            var x = Par{par = x, apply = iApp x}

e :: Term Sig
e = iApp (iLam (\x -> iApp x x)) (iLam (\y -> y))

e' :: Term Sig
e' = parRed e


--------------------------------------------------------------------------------
-- CPS translation
--------------------------------------------------------------------------------

data CPS f = CPS{cpsmeta :: (Term f -> Term f) -> Term f,
                 cpsobj :: Term f -> Term f}

class CPSTrans f v where
  cpsTransAlg :: Alg f (CPS v)

$(derive [liftSum] [''CPSTrans])

cpsTrans :: (Difunctor f, CPSTrans f v, Lam :<: v, App :<: v) => Term f -> Term v
cpsTrans t = iLam (\a -> cpsmeta (cata cpsTransAlg t) (\m -> iApp a m))

instance (App :<: v, Lam :<: v) => CPSTrans App v where
  cpsTransAlg (App x y) = CPS{cpsmeta = \k -> appexp (iLam k),
                              cpsobj = appexp}
    where appexp c = cpsmeta x (\y1 -> cpsmeta y (\y2 -> iApp (iApp y1 y2) c))

instance (Lam :<: v, App :<: v) => CPSTrans Lam v where
  cpsTransAlg (Lam f) = value (iLam (iLam . cpsobj . f . value))
    where value x = CPS{cpsmeta = \k -> k x, cpsobj = \c -> iApp c x}

e1 :: Term Sig
e1 = iLam (\x -> iApp x x)

e1' :: Term Sig
e1' = cpsTrans e1