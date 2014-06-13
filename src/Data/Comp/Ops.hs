{-# LANGUAGE TypeOperators, MultiParamTypeClasses,
             FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
             ScopedTypeVariables, FunctionalDependencies, UndecidableInstances,
             TypeFamilies, DataKinds, ConstraintKinds, PolyKinds #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Ops
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on functors.
--
--------------------------------------------------------------------------------

module Data.Comp.Ops where

import Data.Foldable
import Data.Traversable

import Control.Applicative
import Control.Monad hiding (sequence, mapM)

import Prelude hiding (foldl, mapM, sequence, foldl1, foldr1, foldr)


-- Sums

infixr 6 :+:


-- |Formal sum of signatures (functors).
data (f :+: g) e = Inl (f e)
                 | Inr (g e)

fromInl :: (f :+: g) e -> Maybe (f e)
fromInl = caseF Just (const Nothing)

fromInr :: (f :+: g) e -> Maybe (g e)
fromInr = caseF (const Nothing) Just 

{-| Utility function to case on a functor sum, without exposing the internal
  representation of sums. -}
caseF :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
{-# INLINE caseF #-}
caseF f g x = case x of
                Inl x -> f x
                Inr x -> g x

instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (Inl e) = Inl (fmap f e)
    fmap f (Inr e) = Inr (fmap f e)

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
    fold (Inl e) = fold e
    fold (Inr e) = fold e
    foldMap f (Inl e) = foldMap f e
    foldMap f (Inr e) = foldMap f e
    foldr f b (Inl e) = foldr f b e
    foldr f b (Inr e) = foldr f b e
    foldl f b (Inl e) = foldl f b e
    foldl f b (Inr e) = foldl f b e
    foldr1 f (Inl e) = foldr1 f e
    foldr1 f (Inr e) = foldr1 f e
    foldl1 f (Inl e) = foldl1 f e
    foldl1 f (Inr e) = foldl1 f e

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
    traverse f (Inl e) = Inl <$> traverse f e
    traverse f (Inr e) = Inr <$> traverse f e
    sequenceA (Inl e) = Inl <$> sequenceA e
    sequenceA (Inr e) = Inr <$> sequenceA e
    mapM f (Inl e) = Inl `liftM` mapM f e
    mapM f (Inr e) = Inr `liftM` mapM f e
    sequence (Inl e) = Inl `liftM` sequence e
    sequence (Inr e) = Inr `liftM` sequence e

infixl 5 :<:
infixl 5 :=:

data Pos = Here | Le Pos | Ri Pos | Sum Pos Pos
data Emb = Found Pos | NotFound | Ambiguous

type family Elem (f :: * -> *) (g :: * -> *) :: Emb where
    Elem f f = Found Here
    Elem (f1 :+: f2) g =  Sum' (Elem f1 g) (Elem f2 g) 
    Elem f (g1 :+: g2) = Choose (Elem f g1) (Elem f g2)
    Elem f g = NotFound


type family Choose (e1 :: Emb) (r :: Emb) :: Emb where
    Choose (Found x) (Found y) = Ambiguous
    Choose Ambiguous y = Ambiguous
    Choose x Ambiguous = Ambiguous
    Choose (Found x) y = Found (Le x)
    Choose x (Found y) = Found (Ri y)
    Choose x y = NotFound


type family Sum' (e1 :: Emb) (r :: Emb) :: Emb where
    Sum' (Found x) (Found y) = Found (Sum x y)
    Sum' Ambiguous y = Ambiguous
    Sum' x Ambiguous = Ambiguous
    Sum' NotFound y = NotFound
    Sum' x NotFound = NotFound


type family ComprPos (p :: Pos) :: Pos where
    ComprPos Here = Here
    ComprPos (Le p) = Le (ComprPos p)
    ComprPos (Ri p) = Ri (ComprPos p)
    ComprPos (Sum l r) = CombineMaybe (Sum l r) (Combine (ComprPos l) (ComprPos r))

type family CombineMaybe p p' where
    CombineMaybe p (Just p') = p'
    CombineMaybe p p'        = p

type family Combine (l :: Pos) (r :: Pos) :: Maybe Pos where
    Combine (Le l) (Le r) = Le' (Combine l r)
    Combine (Ri l) (Ri r) = Ri' (Combine l r)
    Combine (Le Here) (Ri Here) = Just Here
    Combine l r = Nothing

type family Ri' p where
    Ri' Nothing = Nothing
    Ri' (Just p) = Just (Ri p)

type family Le' p where
    Le' Nothing = Nothing
    Le' (Just p) = Just (Le p)

type family ComprEmb (e :: Emb) :: Emb where
    ComprEmb (Found p) = Found (ComprPos p)
    ComprEmb e = e

data Proxy a = P

class Subsume (e :: Emb) (f :: * -> *) (g :: * -> *) where
  inj'  :: Proxy e -> f a -> g a
  prj'  :: Proxy e -> g a -> Maybe (f a)

instance Subsume (Found Here) f f where
    inj' _ = id

    prj' _ = Just

instance Subsume (Found p) f g => Subsume (Found (Le p)) f (g :+: g') where
    inj' _ = Inl . inj' (P :: Proxy (Found p))
    
    prj' _ (Inl x) = prj' (P :: Proxy (Found p)) x
    prj' _ _       = Nothing

instance Subsume (Found p) f g => Subsume (Found (Ri p)) f (g' :+: g) where
    inj' _ = Inr . inj' (P :: Proxy (Found p))

    prj' _ (Inr x) = prj' (P :: Proxy (Found p)) x
    prj' _ _       = Nothing
              
instance (Subsume (Found p1) f1 g, Subsume (Found p2) f2 g) 
    => Subsume (Found (Sum p1 p2)) (f1 :+: f2) g where
    inj' _ (Inl x) = inj' (P :: Proxy (Found p1)) x
    inj' _ (Inr x) = inj' (P :: Proxy (Found p2)) x

    prj' _ x = case prj' (P :: Proxy (Found p1)) x of
                 Just y -> Just (Inl y)
                 _      -> case prj' (P :: Proxy (Found p2)) x of
                             Just y -> Just (Inr y)
                             _      -> Nothing


-- | The :<: constraint is a conjunction of two constraints. The first
-- one is used to construct the evidence that is used to implement the
-- injection and projection functions. The first constraint alone
-- would allow instances such as @F :+: F :<: F@ or @F :+: (F :+: G)
-- :<: F :+: G@ which have multiple occurrences of the same
-- sub-signature on the left-hand side. Such instances are usually
-- unintended and yield injection functions that are not
-- injective. The second constraint excludes such instances.
type f :<: g = (Subsume (ComprEmb (Elem f g)) f g)

inj :: forall f g a . (f :<: g) => f a -> g a
inj = inj' (P :: Proxy (ComprEmb (Elem f g)))

proj :: forall f g a . (f :<: g) => g a -> Maybe (f a)
proj = prj' (P :: Proxy (ComprEmb (Elem f g)))

type f :=: g = (f :<: g, g :<: f) 



spl :: (f :=: f1 :+: f2) => (f1 a -> b) -> (f2 a -> b) -> f a -> b
spl f1 f2 x = case inj x of 
            Inl y -> f1 y
            Inr y -> f2 y



-- Products

infixr 8 :*:

-- |Formal product of signatures (functors).
data (f :*: g) a = f a :*: g a


ffst :: (f :*: g) a -> f a
ffst (x :*: _) = x

fsnd :: (f :*: g) a -> g a
fsnd (_ :*: x) = x

-- Constant Products

infixr 7 :&:

{-| This data type adds a constant product (annotation) to a signature. -}
data (f :&: a) e = f e :&: a


instance (Functor f) => Functor (f :&: a) where
    fmap f (v :&: c) = fmap f v :&: c

instance (Foldable f) => Foldable (f :&: a) where
    fold (v :&: _) = fold v
    foldMap f (v :&: _) = foldMap f v
    foldr f e (v :&: _) = foldr f e v
    foldl f e (v :&: _) = foldl f e v
    foldr1 f (v :&: _) = foldr1 f v
    foldl1 f (v :&: _) = foldl1 f v

instance (Traversable f) => Traversable (f :&: a) where
    traverse f (v :&: c) = liftA (:&: c) (traverse f v)
    sequenceA (v :&: c) = liftA (:&: c)(sequenceA v)
    mapM f (v :&: c) = liftM (:&: c) (mapM f v)
    sequence (v :&: c) = liftM (:&: c) (sequence v)

{-| This class defines how to distribute an annotation over a sum of
signatures. -}
class DistAnn s p s' | s' -> s, s' -> p where
    {-| Inject an annotation over a signature. -}
    injectA :: p -> s a -> s' a
    {-| Project an annotation from a signature. -}
    projectA :: s' a -> (s a, p)


class RemA s s' | s -> s'  where
    {-| Remove annotations from a signature. -}
    remA :: s a -> s' a

instance (RemA s s') => RemA (f :&: p :+: s) (f :+: s') where
    remA (Inl (v :&: _)) = Inl v
    remA (Inr v) = Inr $ remA v


instance RemA (f :&: p) f where
    remA (v :&: _) = v


instance DistAnn f p (f :&: p) where

    injectA c v = v :&: c

    projectA (v :&: p) = (v,p)


instance (DistAnn s p s') => DistAnn (f :+: s) p ((f :&: p) :+: s') where


    injectA c (Inl v) = Inl (v :&: c)
    injectA c (Inr v) = Inr $ injectA c v

    projectA (Inl (v :&: p)) = (Inl v,p)
    projectA (Inr v) = let (v',p) = projectA v
                       in  (Inr v',p)
