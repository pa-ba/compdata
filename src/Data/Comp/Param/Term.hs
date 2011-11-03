{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, Rank2Types,
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
-- This module defines the central notion of /parametrised terms/ and their
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
     simpCxt,
     toCxt,
     ParamFunctor(..)
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.Param.Difunctor
import Unsafe.Coerce (unsafeCoerce)

import Data.Maybe (fromJust)

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes, and zero or more parameters. The first
  parameter is a phantom type indicating whether the context has holes. The
  second paramater is the signature of the context, in the form of a
  "Data.Comp.Param.Difunctor". The third parameter is the type of parameters,
  and the fourth parameter is the type of holes. -}
data Cxt :: * -> (* -> * -> *) -> * -> * -> * where
            In :: f a (Cxt h f a b) -> Cxt h f a b
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
simpCxt = In . difmap Hole

toCxt :: Difunctor f => Trm f a -> Cxt h f a b
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

-- Param Functor

{-| Monads for which embedded @Trm@ values, which are parametric at top level,
  can be made into monadic @Term@ values, i.e. \"pushing the parametricity
  inwards\". -}
class ParamFunctor m where
    termM :: (forall a. m (Trm f a)) -> m (Term f)

coerceTermM :: ParamFunctor m => (forall a. m (Trm f a)) -> m (Term f)
{-# INLINE coerceTermM #-}
coerceTermM t = unsafeCoerce t

{-# RULES
    "termM/coerce" termM = coerceTermM
 #-}

instance ParamFunctor Maybe where
    termM Nothing = Nothing
    termM x       = Just (Term $ fromJust x)

instance ParamFunctor (Either a) where
    termM (Left x) = Left x
    termM x        = Right (Term $ fromRight x)
                             where fromRight :: Either a b -> b
                                   fromRight (Right x) = x
                                   fromRight _ = error "fromRight: Left"

instance ParamFunctor [] where
    termM [] = []
    termM l  = Term (head l) : termM (tail l)
