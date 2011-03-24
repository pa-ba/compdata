{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, RankNTypes,
  ScopedTypeVariables, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Term
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of /terms/ and its
-- generalisation to contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Term
    (Cxt (..),
     Hole,
--     NoHole,
--     Context,
     Nothing,
     Term,
     Const,
--     unTerm,
     simpCxt,
     toCxt,
     constTerm,
     (:<)(..)
     ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.Param.Functor
import Unsafe.Coerce

{-|  -}
type Const f = f Nothing ()

{-| This function converts a constant to a term. This assumes that the
argument is indeed a constant, i.e. does not have a value for the
argument type of the functor @f@. -}

constTerm :: (Difunctor f) => Const f -> Term f
constTerm = Term . fmap (const undefined)

{-| This data type represents contexts over a signature. Contexts are
terms containing zero or more holes. The first type parameter is
supposed to be one of the phantom types 'Hole' and 'NoHole'. The
second parameter is the signature of the context. The third parameter
is the type of the holes. -}

data Cxt :: (* -> * -> *) -> * -> * -> * where
            Term :: f a (Cxt f a b) -> Cxt f a b
            Hole :: b -> Cxt f a b


{-| Phantom type that signals that a 'Cxt' might contain holes.  -}

data Hole

{-| Phantom type that signals that a 'Cxt' does not contain holes.
-}

--data NoHole

--type Context = Cxt Hole

{-| Convert a functorial value into a context.  -}
simpCxt :: Difunctor f => f a b -> Cxt f a b
{-# INLINE simpCxt #-}
simpCxt = Term . dimap id Hole


{-| Cast a term over a signature to a context over the same signature. The
  usage of 'unsafeCoerce' is safe, because the empty type 'Nothing' witnesses
  that all uses of the contravariant argument are parametric. -}
toCxt :: Difunctor f => Term f -> Cxt f a a
{-# INLINE toCxt #-}
toCxt = unsafeCoerce
{-toCxt (Term t) = Term $ dimap (unsafeCoerce :: a -> Nothing) toCxt t
toCxt (Hole x) = Hole ((unsafeCoerce :: Nothing -> a) x)-}


{-| Phantom type used to define 'Term'.  -}

data Nothing

instance Eq Nothing where
instance Ord Nothing where
instance Show Nothing where


{-| A (parametrized) term is a context with no /free/ holes, where all
  occurrences of the contravariant parameter is fully parametric. -}
type Term f = Cxt f Nothing Nothing

instance Difunctor f => Difunctor (Cxt f) where
    dimap _ g (Hole v) = Hole (g v)
    dimap f g (Term t) = Term (dimap f (dimap f g) t)

{-instance (Difoldable f) => Difoldable (Cxt h f) where
    foldr op e (Hole a) = a `op` e
    foldr op e (Term t) = foldr op' e t
        where op' c a = foldr op a c

    foldl op e (Hole a) = e `op` a
    foldl op e (Term t) = foldl op' e t
        where op' = foldl op

    fold (Hole a) = a
    fold (Term t) = foldMap fold t

    foldMap f (Hole a) = f a
    foldMap f (Term t) = foldMap (foldMap f) t

instance Ditraversable f => Ditraversable (Cxt h f) where
    dimapM f (Hole a) = liftM Hole $ f a
    dimapM f (Term t) = liftM Term $ dimapM (dimapM f) t

    disequence (Hole a) = liftM Hole a-}

{- {-| This function unravels the given term at the topmost layer.  -}
unTerm :: Cxt NoHole f a e -> f a (Cxt NoHole f a e)
{-# INLINE unTerm #-}
unTerm (Term t) = t-}

class a :< b where
    inj' :: a -> b

instance (:<) a a where
    inj' = id

instance (a :< b) => (:<) a (Cxt f c b) where
    inj' = Hole . inj'

instance (Monad m, a :< b) => (:<) a (m b) where
    inj' = return . inj'