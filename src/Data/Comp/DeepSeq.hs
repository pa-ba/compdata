{-# LANGUAGE GADTs, FlexibleContexts, FlexibleInstances, TypeOperators,
  TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.DeepSeq
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines full evaluation of signatures, which lifts to full
-- evaluation of terms and contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.DeepSeq
    (
     NFDataF(..),
     rnfF'
    )
    where

import Data.Comp.Term
import Control.DeepSeq
import Data.Comp.Derive
import Data.Foldable
import Prelude hiding (foldr)

{-| Fully evaluate a value over a foldable signature. -}
rnfF' :: (Foldable f, NFDataF f, NFData a) => f a -> ()
rnfF' x = foldr seq (rnfF x) x

instance (NFDataF f, NFData a) => NFData (Cxt h f a) where
    rnf (Hole x) = rnf x
    rnf (Term x) = rnfF x

$(derive [liftSum] [''NFDataF])
$(derive [makeNFDataF] [''Maybe, ''[], ''(,)])