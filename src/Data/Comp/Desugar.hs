{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Desugar
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines the 'Desugar' type class for desugaring of terms.
--
--------------------------------------------------------------------------------

module Data.Comp.Desugar where

import Data.Comp
import Data.Comp.Derive

-- |The desugaring term homomorphism.
class (Functor f, Functor g) => Desugar f g where
    desugHom :: TermHom f g
    desugHom = desugHom' . fmap Hole
    desugHom' :: Alg f (Context g a)
    desugHom' x = appCxt (desugHom x)

$(derive [liftSum] [''Desugar])

-- |Desugar a term.
desugar :: (Desugar f g, Traversable f) => Term f -> Term g
{-# INLINE desugar #-}
desugar = appTermHom desugHom

-- |Lift desugaring to annotated terms.
desugarA :: (Traversable f, Traversable f', Functor g, Functor g',
             DistAnn f p f', DistAnn g p g', Desugar f g) => Term f' -> Term g'
desugarA = appTermHom (propAnn desugHom)

-- |Default desugaring instance.
instance (Functor f, Functor g, f :<: g) => Desugar f g where
    desugHom = simpCxt . inj