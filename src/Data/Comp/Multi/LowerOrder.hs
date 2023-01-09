{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Comp.Multi.LowerOrder
    ( LowerOrder (..)
    , lowerOrderSum
    , lowerOrderSumCxt
    , lowerOrderSumTerm
    , lowerOrder
    , lowerOrderCxt
    , lowerOrderTerm
    )
    where

import Data.Comp.Multi
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFoldable
import qualified Data.Comp as C
import qualified Data.Comp.Ops as C
import qualified Data.Comp.Show as C
import Data.Kind

-- |Convert a higher-order functor to an ordinary functor.
data LowerOrder (f :: (Type -> Type) -> Type -> Type) (a :: Type) = forall i . LowerOrder (f (K a) i)

instance HFunctor f => Functor (LowerOrder f) where
    fmap m (LowerOrder f) = LowerOrder $ hfmap (K . m . unK) f

instance HFoldable f => Foldable (LowerOrder f) where
    foldr m z (LowerOrder f) = hfoldr (m . unK) z f

instance (ShowHF f) => C.ShowF (LowerOrder f) where
    showF (LowerOrder x) = unK $ showHF x

type family SummandDecomp (f :: (Type -> Type) -> Type -> Type) :: Type where
    SummandDecomp (f :+: g) = (SummandDecomp f, SummandDecomp g)
    SummandDecomp _ = ()

class RemoveIndex (f :: (Type -> Type) -> Type -> Type) s (g :: Type -> Type) | f s -> g where
    lowerOrderSum' :: forall a b. Proxy s -> f a b -> g (E a)
    lowerOrderSumCxt' :: forall a b h. Proxy s -> Cxt h f a b -> C.Cxt (C h) g (E a)

instance HFunctor f => RemoveIndex f () (LowerOrder f) where
    lowerOrderSum' _ = lowerOrder
    lowerOrderSumCxt' _ (Hole x) = C.Hole $ E x
    lowerOrderSumCxt' _ (Term x) = C.Term . LowerOrder $ hfmap (K . lowerOrderSumCxt' (P @())) x

instance forall s f g s' f' g' . (RemoveIndex f s g, RemoveIndex f' s' g', HFunctor f, HFunctor f', Functor g, Functor g') => RemoveIndex (f :+: f') (s, s') (g C.:+: g') where
    lowerOrderSum' _ (Inl x) = C.Inl $ lowerOrderSum' (P @s) x
    lowerOrderSum' _ (Inr x) = C.Inr $ lowerOrderSum' (P @s') x
    lowerOrderSumCxt' _ (Hole x) = C.Hole $ E x
    lowerOrderSumCxt' _ (Term (Inl x)) = C.Term . C.Inl $ (\(E i) -> lowerOrderSumCxt' (P @(s,s')) i) <$> lowerOrderSum' (P @s) x
    lowerOrderSumCxt' _ (Term (Inr x)) = C.Term . C.Inr $ (\(E i) -> lowerOrderSumCxt' (P @(s,s')) i) <$> lowerOrderSum' (P @s') x

-- |Convert a higher-order functor to an ordinary functor, respecting the summand decomposition.
lowerOrderSum :: forall f g a b . RemoveIndex f (SummandDecomp f) g => f a b -> g (E a)
lowerOrderSum = lowerOrderSum' $ P @(SummandDecomp f)

-- |Convert a context over a higher-order functor to a context over an ordinary functor, respecting the summand decomposition.
lowerOrderSumCxt :: forall f g a b h . RemoveIndex f (SummandDecomp f) g => Cxt h f a b -> C.Cxt (C h) g (E a)
lowerOrderSumCxt = lowerOrderSumCxt' $ P @(SummandDecomp f)

-- |Convert a term over a higher-order functor to a context over an ordinary functor, respecting the summand decomposition.
lowerOrderSumTerm :: forall f g a . Functor g => RemoveIndex f (SummandDecomp f) g => Term f a -> C.Term g
lowerOrderSumTerm = C.toTerm . lowerOrderSumCxt

type family C x where
    C Hole = C.Hole
    C NoHole = C.NoHole

-- |Convert a higher-order functor to an ordinary functor, ignoring the summand decomposition.
lowerOrder :: HFunctor f => f a b -> LowerOrder f (E a)
lowerOrder = LowerOrder . hfmap (K . E)

-- |Convert a context over a higher-order functor to a context over an ordinary functor, ignoring the summand decomposition.
lowerOrderCxt :: HFunctor f => Cxt h f a :=> C.Cxt (C h) (LowerOrder f) (E a)
lowerOrderCxt (Hole x) = C.Hole $ E x
lowerOrderCxt (Term x) = C.Term . LowerOrder $ hfmap (K . lowerOrderCxt) x

-- |Convert a term over a higher-order functor to a term over an ordinary functor, ignoring the summand decomposition.
lowerOrderTerm :: HFunctor f => Term f :=> C.Term (LowerOrder f)
lowerOrderTerm = C.toTerm . lowerOrderCxt
