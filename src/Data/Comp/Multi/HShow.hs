{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, FlexibleContexts,
  ScopedTypeVariables, UndecidableInstances, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.HShow
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  unknown
-- Portability :  unknown
--
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

instance KShow Nothing where
    kshow _ = undefined
instance KShow (K String) where
    kshow = id

instance (HShowF f, HFunctor f) => HShowF (Cxt h f) where
    hshowF (Hole s) = s
    hshowF (Term t) = hshowF $ hfmap hshowF t

instance (HShowF f, HFunctor f, KShow a) => KShow (Cxt h f a) where
    kshow = freeAlgHom hshowF kshow

instance (KShow f) => Show (f i) where
    show = unK . kshow

instance (HShowF f, Show p) => HShowF (f :&&: p) where
    hshowF (v :&&: p) =  K $ (unK $ hshowF v) ++ " :&&: " ++ show p

instance (HShowF f, HShowF g) => HShowF (f :++: g) where
    hshowF (HInl f) = hshowF f
    hshowF (HInr g) = hshowF g