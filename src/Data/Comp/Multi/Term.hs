{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, RankNTypes,
  TypeOperators, ScopedTypeVariables, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Term
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of mutual recursive (or, higher-order)
-- /terms/ and its generalisation to (higher-order) contexts. All definitions
-- are generalised versions of those in "Data.Comp.Term".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Term 
    (HCxt (..),
     HHole,
     HNoHole,
     HContext,
     HNothing,
     HTerm,
     HConst,
     constHTerm,
     unHTerm,
     toHCxt,
     simpHCxt,
     (:.:)(..)
     ) where

import Data.Comp.Multi.HFunctor
import Unsafe.Coerce

type HConst (f :: (* -> *) -> * -> *) = f (K ())

-- | This function converts a constant to a term. This assumes that
-- the argument is indeed a constant, i.e. does not have a value for
-- the argument type of the functor f.

constHTerm :: (HFunctor f) => HConst f :-> HTerm f
constHTerm = HTerm . hfmap (const undefined)

-- | This data type represents contexts over a signature. Contexts are
-- terms containing zero or more holes. The first type parameter is
-- supposed to be one of the phantom types 'HHole' and 'HNoHole'. The
-- second parameter is the signature of the context. The third
-- parameter is the type family of the holes. The last parameter is
-- the index/label.

data HCxt h f a i where
    HTerm ::  f (HCxt h f a) i -> HCxt h f a i
    HHole :: a i -> HCxt HHole f a i

-- | Phantom type that signals that a 'HCxt' might contain holes.
data HHole
-- | Phantom type that signals that a 'HCxt' does not contain holes.
data HNoHole

-- | A context might contain holes.
type HContext = HCxt HHole

{-| Phantom type family used to define 'HTerm'.  -}
data HNothing :: * -> *

instance Show (HNothing i) where
instance Eq (HNothing i) where
instance Ord (HNothing i) where

-- | A (higher-order) term is a context with no holes.
type HTerm f = HCxt HNoHole f HNothing

-- | This function unravels the given term at the topmost layer.
unHTerm :: HTerm f t -> f (HTerm f) t
unHTerm (HTerm t) = t

infixl 5 :.:

-- | This data type denotes the composition of two functor families.
data (f :.: g) e t = Comp f (g e) t

instance (HFunctor f) => HFunctor (HCxt h f) where
    hfmap f (HHole x) = HHole (f x)
    hfmap f (HTerm t) = HTerm (hfmap (hfmap f) t)


simpHCxt :: (HFunctor f) => f a i -> HContext f a i
simpHCxt = HTerm . hfmap HHole

toHCxt :: HTerm f i -> HContext f a i
toHCxt = unsafeCoerce
--toHCxt :: (HFunctor f) => HTerm f i -> HContext f a i
--toHCxt (HTerm t) = HTerm $ hfmap toHCxt t