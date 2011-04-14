{-# LANGUAGE TypeOperators, FlexibleInstances, TypeSynonymInstances,
  IncoherentInstances, UndecidableInstances, TemplateHaskell, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Show
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines showing of signatures, which lifts to showing of terms.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Show
    (
     PShow(..),
     ShowD(..)
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Ops
import Data.Comp.Param.Derive
import Data.Comp.Param.FreshM

instance Show a => PShow a where
    pshow x = return $ show x

instance ShowD (->) where
    showD f = do x <- genVar
                 body <- pshow $ f x
                 return $ "\\" ++ show x ++ " -> " ++ body

-- Lift ShowD to sums
$(derive [liftSum] [''ShowD])

{-| From an 'ShowD' difunctor an 'ShowD' instance of the corresponding term type
  can be derived. -}
instance ShowD f => ShowD (Cxt h f) where
    showD (Term t) = showD t
    showD (Hole h) = pshow h
    showD (Place p) = pshow p

instance (ShowD f, PShow a) => PShow (Cxt h f Var a) where
    pshow = showD

{-| Printing of terms. -}
instance (Difunctor f, ShowD f) => Show (Term f) where
    show x = evalFreshM $ showD $ coerceCxt x

instance (ShowD f, PShow p) => ShowD (f :&: p) where
    showD (x :&: p) = do sx <- showD x
                         sp <- pshow p
                         return $ sx ++ " :&: " ++ sp