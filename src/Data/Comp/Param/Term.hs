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
     Trm,
     Context,
     Const,
     simpCxt,
     coerceCxt,
     toCxt,
     constTerm,
     fmapCxt,
     disequenceCxt,
     dimapMCxt
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.Param.Any
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable
import Control.Monad
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

{-| A context may contain holes, but must be parametric in the bound
  parameters. Parametricity is \"emulated\" using the empty type @Any@, e.g. a
  function of type @Any -> T[Any]@ is equivalent with @forall b. b -> T[b]@,
  but the former avoids the impredicative typing extension, and works also in
  the cases where the codomain type is not a type constructor, e.g.
  @Any -> (Any,Any)@. -}
type Context = Cxt Hole

type Trm f a = Cxt NoHole f a ()

{-| A term is a context with no holes, where all occurrences of the
  contravariant parameter is fully parametric. Parametricity is \"emulated\"
  using the empty type @Any@, e.g. a function of type @Any -> T[Any]@ is
  equivalent with @forall b. b -> T[b]@, but the former avoids the impredicative
  typing extension, and works also in the cases where the codomain type is not a
  type constructor, e.g. @Any -> (Any,Any)@. -}
type Term f = Trm f Any

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

toCxt :: Difunctor f => Trm f a -> Cxt h f a b
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

{-|  -}
type Const f = f Any ()

{-| This function converts a constant to a term. This assumes that the
  argument is indeed a constant, i.e. does not have a value for the
  argument type of the difunctor @f@. -}
constTerm :: Difunctor f => Const f -> Term f
constTerm = Term . fmap (const undefined)

-- | This is an instance of 'fmap' for 'Cxt'.
fmapCxt :: Difunctor f => (b -> b') -> Cxt h f a b -> Cxt h f a b'
fmapCxt f = run
    where run (Term t) = Term $ fmap run t
          run (Place a) = Place a
          run (Hole b)  = Hole $ f b

-- | This is an instance of 'dimamM' for 'Cxt'.
dimapMCxt :: Ditraversable f m a => (b -> m b') -> Cxt h f a b -> m (Cxt h f a b')
dimapMCxt f = run
              where run (Term t)  = liftM Term $ dimapM run t
                    run (Place a) = return $ Place a
                    run (Hole b)  = liftM Hole (f b)

-- | This is an instance of 'disequence' for 'Cxt'.
disequenceCxt :: Ditraversable f m a => Cxt h f a (m b) -> m (Cxt h f a b)
disequenceCxt (Term t)  = liftM Term $ dimapM disequenceCxt t
disequenceCxt (Place a) = return $ Place a
disequenceCxt (Hole b)  = liftM Hole b