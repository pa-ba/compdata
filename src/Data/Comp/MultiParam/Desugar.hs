{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Desugar
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines the 'Desugar' type class for desugaring of terms.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Desugar where

import Data.Comp.MultiParam
import Data.Comp.MultiParam.Derive

-- |The desugaring term homomorphism.
class (HDifunctor f, HDifunctor g) => Desugar f g where
    desugHom :: TermHom f g
    desugHom = desugHom' . fmap Hole
    desugHom' :: f a (Cxt h g a b) -> Cxt h g a b
    desugHom' x = appCxt (desugHom x)

$(derive [liftSum] [''Desugar])

-- |Desugar a term.
desugar :: (Desugar f g, HDifunctor f) => Term f -> Term g
desugar = appTermHom desugHom

-- |Lift desugaring to annotated terms.
desugarA :: (HDifunctor f, HDifunctor f', HDifunctor g, HDifunctor g',
             DistAnn f p f', DistAnn g p g', Desugar f g) => Term f' -> Term g'
desugarA = appTermHom (propAnn desugHom)

-- |Default desugaring instance.
instance (HDifunctor f, HDifunctor g, f :<: g) => Desugar f g where
    desugHom = simpCxt . inj