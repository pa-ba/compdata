{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, RankNTypes,
TypeOperators, ScopedTypeVariables, IncoherentInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Term
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines the central notion of mutual recursive /terms/
-- and its generalisation to contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Term 
    (Cxt (..),
     Hole,
     NoHole,
     Context,
     Nothing,
     Term,
     Const,
     constTerm,
     unTerm,
     toCxt,
     simpCxt,
     (:.:)(..)
     ) where

import Data.Comp.Multi.HFunctor

type Const (f :: (* -> *) -> * -> *) = f (K ())

-- | This function converts a constant to a term. This assumes that
-- the argument is indeed a constant, i.e. does not have a value for
-- the argument type of the functor f.

constTerm :: (HFunctor f) => Const f :-> Term f
constTerm = Term . hfmap (const undefined)

-- | This data type represents contexts over a signature. Contexts are
-- terms containing zero or more holes. The first type parameter is
-- supposed to be one of the phantom types 'Hole' and 'NoHole'. The
-- second parameter is the signature of the context. The third
-- parameter is the type family of the holes. The last parameter is
-- the index/label.

data Cxt h f a i where
    Term ::  f (Cxt h f a) i -> Cxt h f a i
    Hole :: a i -> Cxt Hole f a i

-- | Phantom type that signals that a 'Cxt' might contain holes.
data Hole
-- | Phantom type that signals that a 'Cxt' does not contain holes.
data NoHole

-- | A context might contain holes.
type Context = Cxt Hole

{-| Phantom type family used to define 'Term'.  -}
data Nothing :: * -> *

instance Show (Nothing i) where
instance Eq (Nothing i) where
instance Ord (Nothing i) where

-- | A term is a context with no holes.
type Term f = Cxt NoHole f Nothing

-- | This function unravels the given term at the topmost layer.
unTerm :: Term f t -> f (Term f) t
unTerm (Term t) = t

infixl 5 :.:

-- | This data type denotes the composition of two functor families.
data (f :.: g) e t = Comp f (g e) t

instance (HFunctor f) => HFunctor (Cxt h f) where
    hfmap f (Hole x) = Hole (f x)
    hfmap f (Term t) = Term (hfmap (hfmap f) t)


simpCxt :: (HFunctor f) => f a i -> Context f a i
simpCxt = Term . hfmap Hole

toCxt :: (HFunctor f) => Term f i -> Context f a i
toCxt (Term t) = Term $ hfmap toCxt t