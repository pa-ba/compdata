{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
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

import Data.Comp.Algebra
import Data.Comp.Annotation
import Data.Comp.Derive (liftSum)
import Data.Comp.Derive.Show
import Data.Comp.Derive.Utils (derive)
import Data.Comp.Term

instance (Functor f, ShowF f) => ShowF (Cxt h f) where
    showF (Hole s) = s
    showF (Term t) = showF $ fmap showF t

instance (Functor f, ShowF f, Show a) => Show (Cxt h f a) where
    show = free showF show

instance (ShowF f, Show p) => ShowF (f :&: p) where
    showF (v :&: p) = showF v ++ " :&: " ++ show p

$(derive [liftSum] [''ShowF])
$(derive [makeShowF] [''Maybe, ''[], ''(,)])

instance (ShowConstr f, Show p) => ShowConstr (f :&: p) where
    showConstr (v :&: p) = showConstr v ++ " :&: " ++ show p

$(derive [liftSum] [''ShowConstr])
