{-# LANGUAGE TypeOperators, GADTs, FlexibleContexts,
  ScopedTypeVariables, UndecidableInstances, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.HShow
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines showing of (higher-order) signatures, which lifts to
-- showing of (higher-order) terms and contexts. All definitions are
-- generalised versions of those in "Data.Comp.Show".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.HShow
    ( HShowF(..)
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Product
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor
import Data.Comp.Derive

instance KShow HNothing where
    kshow _ = undefined
instance KShow (K String) where
    kshow = id

instance (HShowF f, HFunctor f) => HShowF (HCxt h f) where
    hshowF (HHole s) = s
    hshowF (HTerm t) = hshowF $ hfmap hshowF t

instance (HShowF f, HFunctor f, KShow a) => KShow (HCxt h f a) where
    kshow = hfree hshowF kshow

instance (KShow f) => Show (f i) where
    show = unK . kshow

instance (HShowF f, Show p) => HShowF (f :&&: p) where
    hshowF (v :&&: p) =  K $ unK (hshowF v) ++ " :&&: " ++ show p

instance (HShowF f, HShowF g) => HShowF (f :++: g) where
    hshowF (HInl f) = hshowF f
    hshowF (HInr g) = hshowF g