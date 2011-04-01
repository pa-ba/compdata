{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances,
  MultiParamTypeClasses, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Term
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of /parametrized terms/.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Term
    (
     Cxt(..),
     Nothing,
     Term,
     Const,
     simpCxt,
     toCxt,
     constTerm
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.Param.Sub
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable (Nothing)
import Unsafe.Coerce

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes. The first parameter is the signature of the
  context. The second parameter is the type of parameters, and the third
  parameter is the type of holes. (For terms, the type of parameters and the
  type of holes are identical.) -}
data Cxt f a b = Term (f a (Cxt f a b)) | Hole b

{-| A (parametrized) term is a context with no /free/ holes, where all
  occurrences of the contravariant parameter is fully parametric. The type
  approximates the type @forall a. Cxt f a a@ using the empty data type
  'Nothing', thereby avoiding impredicative types. -}
type Term f = Cxt f Nothing Nothing

{-| Convert a difunctorial value into a context. -}
simpCxt :: Difunctor f => f a b -> Cxt f a b
{-# INLINE simpCxt #-}
simpCxt = Term . dimap id Hole

{-| Cast a term over a signature to a context over the same signature. The
  usage of 'unsafeCoerce' is safe, because the empty type 'Nothing' witnesses
  that all uses of the contravariant argument are parametric. -}
toCxt :: Difunctor f => Term f -> forall a. Cxt f a a
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

{-|  -}
type Const f = f Nothing ()

{-| This function converts a constant to a term. This assumes that the
  argument is indeed a constant, i.e. does not have a value for the
  argument type of the difunctor @f@. -}
constTerm :: Difunctor f => Const f -> Term f
constTerm = Term . fmap (const undefined)

instance Difunctor f => Difunctor (Cxt f) where
    dimap _ g (Hole v) = Hole $ g v
    dimap f g (Term t) = Term $ dimap f (dimap f g) t

{-| If @a@ can be coerced into @b@ then @a@ can be coerced into any context with
  holes of type @b@. -}
instance (a :< b) => (:<) a (Cxt f c b) where
    coerce = Hole . coerce