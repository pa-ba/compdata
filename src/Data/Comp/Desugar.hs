{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, OverlappingInstances, TypeOperators #-}
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
import Data.Comp.Ops

-- |The desugaring term homomorphism.
class (Functor f, Functor g) => Desugar f g where
    desugHom :: Hom f g
    desugHom = desugHom' . fmap Hole
    desugHom' :: Alg f (Context g a)
    desugHom' x = appCxt (desugHom x)


instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
    desugHom (Inl x) = desugHom x
    desugHom (Inr x) = desugHom x


-- |Desugar a term.
desugar :: Desugar f g => Term f -> Term g
{-# INLINE desugar #-}
desugar = appHom desugHom

-- |Lift desugaring to annotated terms.
desugarA :: (Functor f', Functor g', DistAnn f p f', DistAnn g p g',
             Desugar f g) => Term f' -> Term g'
desugarA = appHom (propAnn desugHom)

-- |Default desugaring instance.
instance (Functor f, Functor g, f :<: g) => Desugar f g where
    desugHom = simpCxt . inj