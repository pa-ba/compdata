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
     Term(..),
     Trm,
     Context,
     MonadTrm(..),
     simpCxt,
     toCxt
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Maybe (fromJust)
import Data.Comp.Param.Difunctor
import Unsafe.Coerce (unsafeCoerce)

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes, and zero or more parameters. The first
  parameter is a phantom type indicating whether the context has holes. The
  second paramater is the signature of the context, in the form of a
  "Data.Comp.Param.Difunctor". The third parameter is the type of parameters,
  and the fourth parameter is the type of holes. -}
data Cxt :: * -> (* -> * -> *) -> * -> * -> * where
            Node :: f a (Cxt h f a b) -> Cxt h f a b
            Hole :: b -> Cxt Hole f a b
            Var :: a -> Cxt h f a b

{-| Phantom type used to define 'Context'. -}
data Hole

{-| Phantom type used to define 'Term'. -}
data NoHole

{-| A context may contain holes. -}
type Context = Cxt Hole

{-| \"Preterms\" -}
type Trm f a = Cxt NoHole f a ()

{-| A term is a context with no holes, where all occurrences of the
  contravariant parameter is fully parametric. -}
newtype Term f = Term{unTerm :: forall a. Trm f a}

{-| Convert a difunctorial value into a context. -}
simpCxt :: Difunctor f => f a b -> Cxt Hole f a b
{-# INLINE simpCxt #-}
simpCxt = Node . fmap Hole

toCxt :: Difunctor f => Trm f a -> Cxt h f a b
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

{-| Monads for which embedded @Trm@ values, which a parametric at top level, can
  be made into embedded @Term@ values. -}
class Monad m => MonadTrm m where
    coerceTrmM :: (forall a. m (Trm f a)) -> m (Term f)

instance MonadTrm Maybe where
    coerceTrmM Nothing = Nothing
    coerceTrmM x = Just (Term $ fromJust x)

instance MonadTrm [] where
    coerceTrmM [] = []
    coerceTrmM l = Term (head l) : coerceTrmM (tail l)