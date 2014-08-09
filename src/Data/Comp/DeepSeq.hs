{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}
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
     NFDataF(..)
    )
    where

import Control.DeepSeq
import Data.Comp.Annotation
import Data.Comp.Derive
import Data.Comp.Term


instance (NFDataF f, NFData a) => NFData (Cxt h f a) where
    rnf (Hole x) = rnf x
    rnf (Term x) = rnfF x

instance (NFDataF f, NFData a) => NFDataF (f :&: a) where
    rnfF (f :&: a) = rnfF f `seq` rnf a


$(derive [liftSum] [''NFDataF])
$(derive [makeNFDataF] [''Maybe, ''[], ''(,)])
