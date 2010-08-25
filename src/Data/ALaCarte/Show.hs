{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Show
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Show
    ( ShowF(..),
      deriveShowFs,
      deriveShowF
    ) where

import Data.ALaCarte
import Data.ALaCarte.Product
import Data.ALaCarte.Derive.Show


instance (ShowF f) => ShowF (Cxt h f) where
    showF (Hole s) = s
    showF (Term t) = showF $ fmap showF t


instance (ShowF f, Show a) => Show (Cxt h f a) where
    show = freeAlgHom showF show

instance ShowF NilF where
    showF _ = undefined


instance (ShowF f, Show p) => ShowF (f :*: p) where
    showF (v :*: p) = showF v ++ " :*: " ++ show p

instance (ShowF f, ShowF g) => ShowF (f :+: g) where
    showF (Inl f) = showF f
    showF (Inr g) = showF g

$(deriveShowFs $ [''Maybe, ''[], ''(,)])