{-# LANGUAGE EmptyDataDecls       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeSynonymInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Term
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of /terms/ and its
-- generalisation to contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.Term
    (Cxt (..),
     Hole,
     NoHole,
     Context,
     Term,
     PTerm,
     Const,
     unTerm,
     simpCxt,
     toCxt,
     toTerm,
     constTerm
     ) where

import Control.Applicative hiding (Const)
import Control.Monad hiding (mapM, sequence)

import Data.Foldable
import Data.Traversable
import Unsafe.Coerce

import Prelude hiding (foldl, foldl1, foldr, foldr1, mapM, sequence)


{-|  -}
type Const f = f ()

{-| This function converts a constant to a term. This assumes that the
argument is indeed a constant, i.e. does not have a value for the
argument type of the functor @f@. -}

constTerm :: (Functor f) => Const f -> Term f
constTerm = Term . fmap (const undefined)

{-| This data type represents contexts over a signature. Contexts are
terms containing zero or more holes. The first type parameter is
supposed to be one of the phantom types 'Hole' and 'NoHole'. The
second parameter is the signature of the context. The third parameter
is the type of the holes. -}

data Cxt :: * -> (* -> *) -> * -> * where
            Term :: f (Cxt h f a) -> Cxt h f a
            Hole :: a -> Cxt Hole f a


{-| Phantom type that signals that a 'Cxt' might contain holes.  -}

data Hole

{-| Phantom type that signals that a 'Cxt' does not contain holes.
-}

data NoHole

type Context = Cxt Hole

{-| Convert a functorial value into a context.  -}
simpCxt :: Functor f => f a -> Context f a
{-# INLINE simpCxt #-}
simpCxt = Term . fmap Hole


{-| Cast a term over a signature to a context over the same signature. -}
toCxt :: Functor f => Term f -> Cxt h f a
{-# INLINE toCxt #-}
toCxt = unsafeCoerce
-- equivalent to @Term . (fmap toCxt) . unTerm@

{-| A term is a context with no holes.  -}
type Term f = Cxt NoHole f ()

{-| Cast a context with no holes over a signature to a term over the same signature. -}
toTerm :: Functor f => Cxt NoHole f a -> Term f
{-# INLINE toTerm #-}
toTerm = unsafeCoerce
-- equivalent to @Term . (fmap toTerm) . unTerm@

-- | Polymorphic definition of a term. This formulation is more
-- natural than 'Term', it leads to impredicative types in some cases,
-- though.
type PTerm f = forall h a . Cxt h f a

instance Functor f => Functor (Cxt h f) where
    fmap f = run
        where run (Hole v) = Hole (f v)
              run (Term t) = Term (fmap run t)

instance Functor f => Applicative (Context f) where
    pure = Hole
    (<*>) = ap

instance (Functor f) => Monad (Context f) where
    return = Hole
    m >>= f = run m
        where run (Hole v) = f v
              run (Term t) = Term (fmap run t)

instance (Foldable f) => Foldable (Cxt h f) where
    foldr op c a = run a c
        where run (Hole a) e = a `op` e
              run (Term t) e = foldr run e t

    foldl op = run
        where run e (Hole a) = e `op` a
              run e (Term t) = foldl run e t

    fold (Hole a) = a
    fold (Term t) = foldMap fold t

    foldMap f = run
        where run (Hole a) = f a
              run (Term t) = foldMap run t

instance (Traversable f) => Traversable (Cxt h f) where
    traverse f = run
        where run (Hole a) = Hole <$> f a
              run (Term t) = Term <$> traverse run t

    sequenceA (Hole a) = Hole <$> a
    sequenceA (Term t) = Term <$> traverse sequenceA t

    mapM f = run
        where run (Hole a) = liftM Hole $ f a
              run (Term t) = liftM Term $ mapM run t

    sequence (Hole a) = liftM Hole a
    sequence (Term t) = liftM Term $ mapM sequence t



{-| This function unravels the given term at the topmost layer.  -}

unTerm :: Cxt NoHole f a -> f (Cxt NoHole f a)
{-# INLINE unTerm #-}
unTerm (Term t) = t
