{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, RankNTypes,
  MultiParamTypeClasses, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Term
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of /parametrized terms/ and their
-- generalisation to parametrised contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Term
    (
     Cxt(..),
     Hole,
     NoHole,
     U,
     Any,
     Term,
     Context,
     Const,
     simpCxt,
     coerceCxt,
     toCxt,
     constTerm
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.Multi.Functor (hfmap)
--import GHC.Prim (Any)
import Unsafe.Coerce

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes, and zero or more parameters. The first
  parameter is a phantom type indicating whether the context has holes. The
  second paramater is the signature of the context, in the form of a
  "Data.Comp.MultiParam.HDifunctor". The third parameter is the type of
  parameters, and the fourth parameter is the type of holes. -}
data Cxt :: * -> ((* -> *) -> (* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> * where
            Term :: f a (Cxt h f a b) i -> Cxt h f a b i
            Hole :: b i -> Cxt Hole f a b i
            Place :: a i -> Cxt h f a b i

{-| Phantom type used to define 'Context'. -}
data Hole

{-| Phantom type used to define 'Term'. -}
data NoHole

data Any :: * -> *

{-| A context may contain holes, but must be parametric in the bound
  parameters. Parametricity is \"emulated\" using the empty type @Any@, e.g. a
  function of type @Any -> T[Any]@ is equivalent with @forall b. b -> T[b]@,
  but the former avoids the impredicative typing extension, and works also in
  the cases where the codomain type is not a type constructor, e.g.
  @Any -> (Any,Any)@. -}
type Context f = Cxt Hole f Any

-- Unit functor
type U = K ()

{-| A term is a context with no holes, where all occurrences of the
  contravariant parameter is fully parametric. Parametricity is \"emulated\"
  using the empty type @Any@, e.g. a function of type @Any -> T[Any]@ is
  equivalent with @forall b. b -> T[b]@, but the former avoids the impredicative
  typing extension, and works also in the cases where the codomain type is not a
  type constructor, e.g. @Any -> (Any,Any)@. -}
type Term f = Cxt NoHole f Any U

{-| Convert a difunctorial value into a context. -}
simpCxt :: HDifunctor f => f a b i -> Cxt Hole f a b i
{-# INLINE simpCxt #-}
simpCxt = Term . hfmap Hole

{-| Cast a \"pseudo-parametric\" context over a signature to a parametric
  context over the same signature. The usage of 'unsafeCoerce' is safe, because
  the empty type 'Any' witnesses that all uses of the contravariant argument are
  parametric. -}
coerceCxt :: Cxt h f Any b i -> forall a. Cxt h f a b i
coerceCxt = unsafeCoerce

toCxt :: HDifunctor f => Cxt NoHole f a b :-> Cxt h f a b
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

{-|  -}
type Const (f :: (* -> *) -> (* -> *) -> * -> *) = f Any U

{-| This function converts a constant to a term. This assumes that the
  argument is indeed a constant, i.e. does not have a value for the
  argument type of the difunctor @f@. -}
constTerm :: HDifunctor f => Const f :-> Term f
constTerm = Term . hfmap (const undefined)