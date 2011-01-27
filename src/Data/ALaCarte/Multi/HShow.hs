{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, FlexibleContexts,
  ScopedTypeVariables, UndecidableInstances, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Multi.HShow
-- Copyright   :  3gERP, 2011
-- License     :  AllRightsReserved
-- Maintainer  :  Patrick Bahr, Tom Hvitved
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Multi.HShow
    ( HShowF(..)
    ) where

import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.Sum
import Data.ALaCarte.Multi.Product
import Data.ALaCarte.Multi.Algebra
import Data.ALaCarte.Multi.HFunctor
import Data.ALaCarte.Derive

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