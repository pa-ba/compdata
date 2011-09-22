{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
             ScopedTypeVariables, FunctionalDependencies, UndecidableInstances, KindSignatures #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Ops
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on higher-order functors. All definitions are
-- generalised versions of those in "Data.Comp.Ops".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Ops where

import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.HTraversable
import qualified Data.Comp.Ops as O
import Control.Monad
import Control.Applicative


infixr 5 :+:


-- |Data type defining coproducts.
data (f :+: g) (h :: * -> *) e = Inl (f h e)
                    | Inr (g h e)

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
    hfmap f (Inl v) = Inl $ hfmap f v
    hfmap f (Inr v) = Inr $ hfmap f v

instance (HFoldable f, HFoldable g) => HFoldable (f :+: g) where
    hfold (Inl e) = hfold e
    hfold (Inr e) = hfold e
    hfoldMap f (Inl e) = hfoldMap f e
    hfoldMap f (Inr e) = hfoldMap f e
    hfoldr f b (Inl e) = hfoldr f b e
    hfoldr f b (Inr e) = hfoldr f b e
    hfoldl f b (Inl e) = hfoldl f b e
    hfoldl f b (Inr e) = hfoldl f b e

    hfoldr1 f (Inl e) = hfoldr1 f e
    hfoldr1 f (Inr e) = hfoldr1 f e
    hfoldl1 f (Inl e) = hfoldl1 f e
    hfoldl1 f (Inr e) = hfoldl1 f e

instance (HTraversable f, HTraversable g) => HTraversable (f :+: g) where
    htraverse f (Inl e) = Inl <$> htraverse f e
    htraverse f (Inr e) = Inr <$> htraverse f e
    hmapM f (Inl e) = Inl `liftM` hmapM f e
    hmapM f (Inr e) = Inr `liftM` hmapM f e

-- |The subsumption relation.
class (sub :: (* -> *) -> * -> *) :<: sup where
    inj :: sub a :-> sup a
    proj :: NatM Maybe (sup a) (sub a)

instance (:<:) f f where
    inj = id
    proj = Just

instance (:<:) f (f :+: g) where
    inj = Inl
    proj (Inl x) = Just x
    proj (Inr _) = Nothing

instance (f :<: g) => (:<:) f (h :+: g) where
    inj = Inr . inj
    proj (Inr x) = proj x
    proj (Inl _) = Nothing

-- Products

infixr 8 :*:

data (f :*: g) a = f a :*: g a


fst :: (f :*: g) a -> f a
fst (x :*: _) = x

snd :: (f :*: g) a -> g a
snd (_ :*: x) = x

-- Constant Products

infixr 7 :&:

-- | This data type adds a constant product to a
-- signature. Alternatively, this could have also been defined as
-- 
-- @data (f :&: a) (g ::  * -> *) e = f g e :&: a e@
-- 
-- This is too general, however, for example for 'productHHom'.

data (f :&: a) (g ::  * -> *) e = f g e :&: a


instance (HFunctor f) => HFunctor (f :&: a) where
    hfmap f (v :&: c) = hfmap f v :&: c

instance (HFoldable f) => HFoldable (f :&: a) where
    hfold (v :&: _) = hfold v
    hfoldMap f (v :&: _) = hfoldMap f v
    hfoldr f e (v :&: _) = hfoldr f e v
    hfoldl f e (v :&: _) = hfoldl f e v
    hfoldr1 f (v :&: _) = hfoldr1 f v
    hfoldl1 f (v :&: _) = hfoldl1 f v


instance (HTraversable f) => HTraversable (f :&: a) where
    htraverse f (v :&: c) =  (:&: c) <$> (htraverse f v)
    hmapM f (v :&: c) = liftM (:&: c) (hmapM f v)

-- | This class defines how to distribute an annotation over a sum of
-- signatures.
class DistAnn (s :: (* -> *) -> * -> *) p s' | s' -> s, s' -> p where
    -- | This function injects an annotation over a signature.
    injectA :: p -> s a :-> s' a
    projectA :: s' a :-> (s a O.:&: p)


class RemA (s :: (* -> *) -> * -> *) s' | s -> s'  where
    remA :: s a :-> s' a


instance (RemA s s') => RemA (f :&: p :+: s) (f :+: s') where
    remA (Inl (v :&: _)) = Inl v
    remA (Inr v) = Inr $ remA v


instance RemA (f :&: p) f where
    remA (v :&: _) = v


instance DistAnn f p (f :&: p) where

    injectA p v = v :&: p

    projectA (v :&: p) = v O.:&: p


instance (DistAnn s p s') => DistAnn (f :+: s) p ((f :&: p) :+: s') where
    injectA p (Inl v) = Inl (v :&: p)
    injectA p (Inr v) = Inr $ injectA p v

    projectA (Inl (v :&: p)) = (Inl v O.:&: p)
    projectA (Inr v) = let (v' O.:&: p) = projectA v
                        in  (Inr v' O.:&: p)