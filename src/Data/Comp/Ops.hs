{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
             ScopedTypeVariables, FunctionalDependencies, UndecidableInstances,
             TypeFamilies, DataKinds, ConstraintKinds #-}

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

data Pos = Here | GoLeft Pos | GoRight Pos | Sum Pos Pos
data Emb = NotFound | Ambiguous | Found Pos


type family GetEmb (f :: * -> *) (g :: * -> *) :: Emb where
    GetEmb f f = Found Here
    GetEmb f (g1 :+: g2) = Pick f (g1 :+: g2) (GetEmb f g1) (GetEmb f g2)
    GetEmb f g = NotFound


type family Pick f g (e1 :: Emb) (r :: Emb) :: Emb where
    Pick f g (Found x) (Found y) = Ambiguous
    Pick f g Ambiguous y = Ambiguous
    Pick f g x Ambiguous = Ambiguous
    Pick f g (Found x) y = Found (GoLeft x)
    Pick f g x (Found y) = Found (GoRight y)
    Pick f g x y = Split f g

type family Split (f :: * -> *) (g :: * -> *) :: Emb where
    Split (f1 :+: f2) g = Pick2 (GetEmb f1 g) (GetEmb f2 g) 
    Split f g = NotFound

type family Pick2 (e1 :: Emb) (r :: Emb) :: Emb where
    Pick2 (Found x) (Found y) = Found (Sum x y)
    Pick2 Ambiguous y = Ambiguous
    Pick2 x Ambiguous = Ambiguous
    Pick2 NotFound y = NotFound
    Pick2 x NotFound = NotFound

data EmbD (e :: Emb) (f :: * -> *) (g :: * -> *) where
    HereD :: EmbD (Found Here) f f
    GoLeftD :: EmbD (Found p) f g -> EmbD (Found (GoLeft p)) f (g :+: g')
    GoRightD :: EmbD (Found p) f g -> EmbD (Found (GoRight p)) f (g' :+: g)
    SumD :: EmbD (Found p1) f1 g -> EmbD (Found p2) f2 g -> EmbD (Found (Sum p1 p2)) (f1 :+: f2) g

class GetEmbD (e :: Emb) (f :: * -> *) (g :: * -> *) where
    getEmbD :: EmbD e f g

instance GetEmbD (Found Here) f f where
    getEmbD = HereD

instance GetEmbD (Found p) f g => GetEmbD (Found (GoLeft p)) f (g :+: g') where
    getEmbD = GoLeftD getEmbD

instance GetEmbD (Found p) f g => GetEmbD (Found (GoRight p)) f (g' :+: g) where
    getEmbD = GoRightD getEmbD

instance (GetEmbD (Found p1) f1 g, GetEmbD (Found p2) f2 g) 
    => GetEmbD (Found (Sum p1 p2)) (f1 :+: f2) g where
    getEmbD = SumD getEmbD getEmbD


-- The following definitions are used to reject instances of :<: such
-- as @F :+: F :<: F@ or @F :+: (F :+: G) :<: F :+: G@.

data SimpPos = SimpHere | SimpLeft SimpPos | SimpRight SimpPos

data Res = CompPos SimpPos Pos | SingPos SimpPos


type family DestrPos (e :: Pos) :: Res where
    DestrPos (GoLeft e) = ResLeft (DestrPos e)
    DestrPos (GoRight e) = ResRight (DestrPos e)
    DestrPos (Sum e1 e2) = ResSum (DestrPos e1) e2
    DestrPos Here = SingPos SimpHere

type family ResLeft (r :: Res) :: Res where
    ResLeft (CompPos p e) = CompPos (SimpLeft p) (GoLeft e)
    ResLeft (SingPos p) = SingPos (SimpLeft p)

type family ResRight (r :: Res) :: Res where
    ResRight (CompPos p e) = CompPos (SimpRight p) (GoRight e)
    ResRight (SingPos p) = SingPos (SimpRight p)

type family ResSum (r :: Res) (e :: Pos) :: Res where
    ResSum (CompPos p e1) e2 = CompPos p (Sum e1 e2)
    ResSum (SingPos p) e = CompPos p e

type family Or x y where
    Or x False = x
    Or False y = y
    Or x y  = True

type family In (p :: SimpPos) (e :: Pos) :: Bool where
    In SimpHere e = True
    In p Here = True
    In (SimpLeft p) (GoLeft e) = In p e
    In (SimpRight p) (GoRight e) = In p e
    In p (Sum e1 e2) = Or (In p e1)  (In p e2)
    In p e = False

type family Duplicates' (r :: Res) :: Bool where
    Duplicates' (SingPos p) = False
    Duplicates' (CompPos p e) = Or (In p e) (Duplicates' (DestrPos e))

type family Duplicates (e :: Emb) where
    Duplicates (Found p) = Duplicates' (DestrPos p)

-- This class is used to produce more informative error messages
class NoDup (b :: Bool) (f :: * -> *) (g :: * -> *)
instance NoDup False f g

inj_ :: EmbD e f g -> f a -> g a
inj_ HereD x = x
inj_ (GoLeftD e) x = Inl (inj_ e x)
inj_ (GoRightD e) x = Inr (inj_ e x)
inj_ (SumD e1 e2) x = case x of
                        Inl y -> inj_ e1 y
                        Inr y -> inj_ e2 y

-- | The :<: constraint is a conjunction of two constraints. The first
-- one is used to construct the evidence that is used to implement the
-- injection and projection functions. The first constraint alone
-- would allow instances such as @F :+: F :<: F@ or @F :+: (F :+: G)
-- :<: F :+: G@ which have multiple occurrences of the same
-- sub-signature on the left-hand side. Such instances are usually
-- unintended and yield injection functions that are not
-- injective. The second constraint excludes such instances.
type f :<: g = (GetEmbD (GetEmb f g) f g, NoDup (Duplicates (GetEmb f g)) f g)

inj :: forall f g a . (f :<: g) => f a -> g a
inj = inj_ (getEmbD :: EmbD (GetEmb f g) f g)

type f :=: g = (f :<: g, g :<: f) 


proj_ :: EmbD e f g -> g a -> Maybe (f a)
proj_ HereD x = Just x
proj_ (GoLeftD p) x = case x of 
                        Inl y -> proj_ p y
                        _ -> Nothing
proj_ (GoRightD p) x = case x of 
                          Inr x -> proj_ p x
                          _ -> Nothing
proj_ (SumD p1 p2) x = case proj_ p1 x of
                         Just y -> Just (Inl y)
                         _ -> case proj_ p2 x of
                                Just y -> Just (Inr y)
                                _ -> Nothing


proj :: forall f g a . (f :<: g) => g a -> Maybe (f a)
proj = proj_ (getEmbD :: EmbD (GetEmb f g) f g)

spl :: (f :<: f1 :+: f2) => (f1 a -> b) -> (f2 a -> b) -> f a -> b
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
