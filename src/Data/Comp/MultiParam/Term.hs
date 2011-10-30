{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, Rank2Types,
  MultiParamTypeClasses, TypeOperators, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Term
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of /generalised parametrised terms/
-- and their generalisation to generalised parametrised contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Term
    (
     Cxt(..),
     Hole,
     NoHole,
     Term(..),
     Trm,
     Context,
     simpCxt,
     toCxt,
     hfmapCxt,
     hdimapMCxt
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.HDitraversable
import Control.Monad 
import Unsafe.Coerce

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes, and zero or more parameters. The first
  parameter is a phantom type indicating whether the context has holes. The
  second paramater is the signature of the context, in the form of a
  "Data.Comp.MultiParam.HDifunctor". The third parameter is the type of
  parameters, the fourth parameter is the type of holes, and the fifth
  parameter is the GADT type. -}
data Cxt :: * -> ((* -> *) -> (* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> * where
            In :: f a (Cxt h f a b) i -> Cxt h f a b i
            Hole :: b i -> Cxt Hole f a b i
            Var :: a i -> Cxt h f a b i

{-| Phantom type used to define 'Context'. -}
data Hole

{-| Phantom type used to define 'Term'. -}
data NoHole

{-| A context may contain holes. -}
type Context = Cxt Hole

{-| \"Preterms\" |-}
type Trm f a = Cxt NoHole f a (K ())

{-| A term is a context with no holes, where all occurrences of the
  contravariant parameter is fully parametric. -}
newtype Term f i = Term{unTerm :: forall a. Trm f a i}

{-| Convert a difunctorial value into a context. -}
simpCxt :: HDifunctor f => f a b :-> Cxt Hole f a b
{-# INLINE simpCxt #-}
simpCxt = In . hfmap Hole

toCxt :: HDifunctor f => Trm f a :-> Cxt h f a b
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

-- | This is an instance of 'hfmap' for 'Cxt'.
hfmapCxt :: forall h f a b b'. HDifunctor f
         => (b :-> b') -> Cxt h f a b :-> Cxt h f a b'
hfmapCxt f = run
    where run :: Cxt h f a b :-> Cxt h f a b'
          run (In t)   = In $ hfmap run t
          run (Var a)  = Var a
          run (Hole b) = Hole $ f b

-- | This is an instance of 'hdimapM' for 'Cxt'.
hdimapMCxt :: forall h f a b b' m . HDitraversable f m
          => NatM m b b' -> NatM m (Cxt h f a b) (Cxt h f a b')
hdimapMCxt f = run
    where run :: NatM m (Cxt h f a b) (Cxt h f a b')
          run (In t)   = liftM In $ hdimapM run t
          run (Var a)  = return $ Var a
          run (Hole b) = liftM Hole (f b)