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
     PShow(..),
     ShowHD(..)
    ) where

import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.Derive
import Data.Comp.MultiParam.FreshM

instance Show a => PShow (K a) where
    pshow = return . show . unK

-- Lift ShowHD to sums
$(derive [liftSum] [''ShowHD])

instance PShow Var where
    pshow = return . varShow

{-| From an 'ShowHD' higher-order difunctor an 'ShowHD' instance of the
  corresponding term type can be derived. -}
instance (ShowHD f, PShow a) => PShow (Cxt h f Var a) where
    pshow (Term t) = showHD t
    pshow (Hole h) = pshow h
    pshow (Place p) = pshow p

{-| Printing of terms. -}
instance (HDifunctor f, ShowHD f) => Show (Term f i) where
    show = evalFreshM . pshow .
           (coerceCxt :: Term f i -> Cxt NoHole f Var (K ()) i)

instance (ShowHD f, PShow (K p)) => ShowHD (f :&: p) where
    showHD (x :&: p) = do sx <- showHD x
                          sp <- pshow $ K p
                          return $ sx ++ " :&: " ++ sp