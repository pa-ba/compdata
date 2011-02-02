{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, TypeSynonymInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Show
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
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
    show = freeAlgHom showF show

instance (ShowF f, Show p) => ShowF (f :&: p) where
    showF (v :&: p) = showF v ++ " :&: " ++ show p

instance (ShowF f, ShowF g) => ShowF (f :+: g) where
    showF (Inl f) = showF f
    showF (Inr g) = showF g

$(derive [instanceShowF] $ [''Maybe, ''[], ''(,)])