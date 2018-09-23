{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ConstraintKinds  #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Decompose
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements the decomposition of terms into function
-- symbols and arguments resp. variables.
--
--------------------------------------------------------------------------------
module Data.Comp.Decompose (
  Decomp (..),
  DecompTerm,
  Decompose,
  decomp,
  structure,
  arguments,
  decompose
  ) where

import Data.Comp.Term
import Data.Comp.Variables
import Data.Foldable

{-| This function computes the structure of a functorial value. -}

structure :: (Functor f) => f a -> Const f
structure = fmap (const ())

{-| This function computes the arguments of a functorial value.  -}

arguments :: (Foldable f) => f a -> [a]
arguments = toList

{-| This type represents decompositions of functorial values. -}

data Decomp f v a = Var v
                  | Fun (Const f) [a]

{-| This type represents decompositions of terms.  -}

type DecompTerm f v = Decomp f v (Term f)

{-| This class specifies the decomposability of a functorial value. -}

type Decompose f v = (HasVars f v, Functor f, Foldable f)

decomp :: Decompose f v => f a -> Decomp f v a
decomp t = case isVar t of
             Just v -> Var v
             Nothing -> Fun sym args
               where sym = fmap (const ()) t
                     args = arguments t


{-| This function decomposes a term. -}

decompose :: Decompose f v => Term f -> DecompTerm f v
decompose (Term t) = decomp t
