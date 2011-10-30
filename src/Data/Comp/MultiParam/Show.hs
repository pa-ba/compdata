{-# LANGUAGE TypeOperators, FlexibleInstances, TypeSynonymInstances,
  IncoherentInstances, UndecidableInstances, TemplateHaskell, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Show
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines showing of signatures, which lifts to showing of terms.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam.Show
    (
     ShowHD(..)
    ) where

import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.Derive
import Data.Comp.MultiParam.FreshM

-- Lift ShowHD to sums
$(derive [liftSum] [''ShowHD])

{-| From an 'ShowHD' higher-order difunctor an 'ShowHD' instance of the
  corresponding term type can be derived. -}
instance (HDifunctor f, ShowHD f) => ShowHD (Cxt h f) where
    showHD (In t) = showHD $ hfmap (K . showHD) t
    showHD (Hole h) = unK h
    showHD (Var p) = return $ show p

{-| Printing of terms. -}
instance (HDifunctor f, ShowHD f) => Show (Term f i) where
    show = evalFreshM . showHD . toCxt . unTerm

instance (ShowHD f, Show p) => ShowHD (f :&: p) where
    showHD (x :&: p) = do sx <- showHD x
                          return $ sx ++ " :&: " ++ show p