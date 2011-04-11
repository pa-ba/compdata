{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, TypeOperators, OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Desugar
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines the 'Desugar' type class for desugaring of terms.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Desugar where

import Data.Comp.Multi
import Data.Comp.Multi.Derive

-- |The desugaring term homomorphism.
class (HFunctor f, HFunctor g) => Desugar f g where
  desugHom :: TermHom f g
  desugHom = desugHom' . hfmap Hole
  desugHom' :: Alg f (Context g a)
  desugHom' x = appCxt (desugHom x)

$(derive [liftSum] [''Desugar])

-- |Desugar a term.
desugar :: (Desugar f g, HFunctor f) => Term f :-> Term g
desugar = appTermHom desugHom

-- |Lift desugaring to annotated terms.
desugarA :: (HFunctor f, HFunctor f', HFunctor g, HFunctor g',
             DistAnn f p f', DistAnn g p g', Desugar f g) => Term f' :-> Term g'
desugarA = appTermHom (propAnn desugHom)

-- |Default desugaring instance.
instance (HFunctor f, HFunctor g, f :<: g) => Desugar f g where
  desugHom = simpCxt . inj