{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, TypeSynonymInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Show
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines showing of signatures, which lifts to showing of
-- terms and contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.Show
    ( ShowF(..)
    ) where

import Data.Comp.Term
import Data.Comp.Sum
import Data.Comp.Product
import Data.Comp.Algebra
import Data.Comp.Derive

instance (Functor f, ShowF f) => ShowF (Cxt h f) where
    showF (Hole s) = s
    showF (Term t) = showF $ fmap showF t

instance (Functor f, ShowF f, Show a) => Show (Cxt h f a) where
    show = free showF show

instance (ShowF f, Show p) => ShowF (f :&: p) where
    showF (v :&: p) = showF v ++ " :&: " ++ show p

instance (ShowF f, ShowF g) => ShowF (f :+: g) where
    showF (Inl f) = showF f
    showF (Inr g) = showF g

$(derive [instanceShowF] [''Maybe, ''[], ''(,)])