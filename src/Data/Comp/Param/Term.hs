{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, RankNTypes,
  MultiParamTypeClasses #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Term
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

module Data.Comp.Param.Term
    (
     Cxt(..),
     Hole,
     NoHole,
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
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable
import Data.Maybe (fromJust)
import Unsafe.Coerce

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes, and zero or more parameters. The first
  parameter is a phantom type indicating whether the context has holes. The
  second paramater is the signature of the context, in the form of a
  "Data.Comp.Param.Difunctor". The third parameter is the type of parameters,
  and the fourth parameter is the type of holes. -}
data Cxt :: * -> (* -> * -> *) -> * -> * -> * where
            Term :: f a (Cxt h f a b) -> Cxt h f a b
            Hole :: b -> Cxt Hole f a b
            Place :: a -> Cxt h f a b

{-| Phantom type used to define 'Context'. -}
data Hole

{-| Phantom type used to define 'Term'. -}
data NoHole

{-| An empty type. @Any@ is used to emulate parametricity, e.g. a function of
  type @Any -> T[Any]@ is equivalent with @forall b. b -> T[b]@, but the
  former avoids the impredicative typing extension, and works also in the
  cases where the codomain type is not a type constructor, e.g.
  @Any -> (Any,Any)@. -}
data Any

instance Eq Any where
instance Ord Any where
instance Show Any where

{-| A context may contain holes, but must be parametric in the bound
  parameters. -}
type Context f = Cxt Hole f Any

{-| A term is a context with no holes, where all occurrences of the
  contravariant parameter is fully parametric. The type approximates the
  type @forall h a b. Cxt h f a b@ using the empty data types 'Any' and
  'NoHole', thereby avoiding impredicative types. -}
type Term f = Cxt NoHole f Any ()

{-| Convert a difunctorial value into a context. -}
simpCxt :: Difunctor f => f a b -> Cxt Hole f a b
{-# INLINE simpCxt #-}
simpCxt = Term . fmap Hole

{-| Cast a \"pseudo-parametric\" context over a signature to a parametric
  context over the same signature. The usage of 'unsafeCoerce' is safe, because
  the empty type 'Any' witnesses that all uses of the contravariant argument are
  parametric. -}
coerceCxt :: Cxt h f Any b -> forall a. Cxt h f a b
coerceCxt = unsafeCoerce

toCxt :: Difunctor f => Cxt NoHole f a b -> Cxt h f a b
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

{-|  -}
type Const f = f Any ()

{-| This function converts a constant to a term. This assumes that the
  argument is indeed a constant, i.e. does not have a value for the
  argument type of the difunctor @f@. -}
constTerm :: Difunctor f => Const f -> Term f
constTerm = Term . fmap (const undefined)

{-| Functions of the type @Any -> Maybe a@ can be turned into functions of
 type @Maybe (Any -> a)@. The empty type @Any@ ensures that the function
 is parametric in the input, and hence the @Maybe@ monad can be pulled out. -}
instance Ditraversable (->) Maybe Any where
    disequence f = do _ <- f undefined
                      return $ \x -> fromJust $ f x