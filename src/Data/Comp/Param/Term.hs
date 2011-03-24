{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, RankNTypes,
  ScopedTypeVariables, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Term
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of /parametrized terms/ and its
-- generalisation to contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Term
    (
     Cxt (..),
     Nothing,
     Term,
     Const,
     simpCxt,
     toCxt,
     constTerm,
     substHoles,
     substHoles'
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.Param.Functor
import Data.Comp.Param.Ops
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Unsafe.Coerce

{-|  -}
type Const f = f Nothing ()

{-| This function converts a constant to a term. This assumes that the
  argument is indeed a constant, i.e. does not have a value for the
  argument type of the difunctor @f@. -}
constTerm :: Difunctor f => Const f -> Term f
constTerm = Term . fmap (const undefined)

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes. The first parameter is the signature of the
  context. The second parameter is the type of parameters, and the third
  parameter is the type of holes. -}
data Cxt :: (* -> * -> *) -> * -> * -> * where
            Term :: f a (Cxt f a b) -> Cxt f a b
            Hole :: b -> Cxt f a b

{-| Convert a difunctorial value into a context. -}
simpCxt :: Difunctor f => f a b -> Cxt f a b
{-# INLINE simpCxt #-}
simpCxt = Term . dimap id Hole

{-| Cast a term over a signature to a context over the same signature. The
  usage of 'unsafeCoerce' is safe, because the empty type 'Nothing' witnesses
  that all uses of the contravariant argument are parametric. -}
toCxt :: Difunctor f => Term f -> Cxt f a a
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

{-| Phantom type used to define 'Term'.  -}
data Nothing

instance Eq Nothing where
instance Ord Nothing where
instance Show Nothing where

{-| A (parametrized) term is a context with no /free/ holes, where all
  occurrences of the contravariant parameter is fully parametric. -}
type Term f = Cxt f Nothing Nothing

{-| This function applies the given context with hole type @b@ to a family @f@
  of contexts (possibly terms) indexed by @b@. That is, each hole @h@ is
  replaced by the context @f h@. -}
substHoles :: (Difunctor f, Difunctor g, f :<: g)
           => Cxt f a b -> (b -> Cxt g a c) -> Cxt g a c
substHoles c f = injectCxt $ fmap f c
    where injectCxt (Hole x) = x
          injectCxt (Term t) = Term . inj $ fmap injectCxt t

{-| Variant of 'substHoles' using 'Map's. -}
substHoles' :: (Difunctor f, Difunctor g, f :<: g, Ord v)
            => Cxt f p v -> Map v (Cxt g p a) -> Cxt g p a
substHoles' c m = substHoles c (fromJust . (`Map.lookup`  m))

instance Difunctor f => Difunctor (Cxt f) where
    dimap _ g (Hole v) = Hole $ g v
    dimap f g (Term t) = Term $ dimap f (dimap f g) t

instance Difunctor f => Monad (Cxt f a) where
    return = Hole
    (>>=) = substHoles