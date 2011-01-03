{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, TypeOperators, TemplateHaskell #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.DeepSeq
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.DeepSeq where

import Data.ALaCarte.Term
import Data.ALaCarte.Sum
import Control.DeepSeq
import Data.ALaCarte.Derive
import Data.Foldable
import Prelude hiding (foldr)


rnfF' :: (Foldable f, NFDataF f, NFData a) => f a -> ()
rnfF' x = foldr seq (rnfF x) x

instance (NFDataF f, NFData a) => NFData (Cxt h f a) where
    rnf (Hole x) = rnf x
    rnf (Term x) = rnfF x

instance (NFDataF f, NFDataF g) => NFDataF (f:+:g) where
    rnfF (Inl v) = rnfF v
    rnfF (Inr v) = rnfF v

instance NFData Nothing where


$(derive [instanceNFDataF] $ [''Maybe, ''[], ''(,)])