{-# LANGUAGE GADTs, RankNTypes, TypeOperators, ScopedTypeVariables, 
  FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Algebra
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the notion of algebras and catamorphisms, and their
-- generalizations to e.g. monadic versions and other (co)recursion schemes.
-- All definitions are generalised versions of those in "Data.Comp.Algebra".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Algebra (
      -- * Algebras & Catamorphisms
      HAlg,
      hfree,
      hcata,
      hcata',
      appHCxt,
      
      -- * Monadic Algebras & Catamorphisms
      HAlgM,
--      halgM,
      hfreeM,
      hcataM,
      hcataM',

      -- * Term Homomorphisms
      HCxtFun,
      HSigFun,
      HTermHom,
      appHTermHom,
      compHTermHom,
      appHSigFun,
      compHSigFun,
      htermHom,
      compHAlg,
--      compHCoalg,
--      compHCVCoalg,

      -- * Monadic Term Homomorphisms
      HCxtFunM,
      HSigFunM,
      HTermHomM,
--      HSigFunM',
--      HTermHomM',
      hsigFunM,
--      htermHom',
      appHTermHomM,
      htermHomM,
--      htermHomM',
      appHSigFunM,
--      appHSigFunM',
      compHTermHomM,
      compHSigFunM,
      compHAlgM,
      compHAlgM',

      -- * Coalgebras & Anamorphisms
      HCoalg,
      hana,
--      hana',
      HCoalgM,
      hanaM,

      -- * R-Algebras & Paramorphisms
      HRAlg,
      hpara,
      HRAlgM,
      hparaM,

      -- * R-Coalgebras & Apomorphisms
      HRCoalg,
      hapo,
      HRCoalgM,
      hapoM,

      -- * CV-Algebras & Histomorphisms
      -- $l1
--      HCVAlg,
--      hhisto,
--      HCVAlgM,
--      hhistoM,

      -- * CV-Coalgebras & Futumorphisms
      HCVCoalg,
      hfutu,
--      HCVCoalg',
--      hfutu',
      HCVCoalgM,
      hfutuM,

      -- * Exponential Functors
      appHTermHomE,
      hcataE,
--      hanaE,
      appHCxtE
    ) where


import Data.Comp.Multi.Term
import Data.Comp.Multi.Functor
import Data.Comp.Multi.Traversable
import Data.Comp.Multi.ExpFunctor
import Data.Comp.Ops

import Control.Monad


type HAlg f e = f e :-> e

hfree :: forall f h a b . (HFunctor f) =>
              HAlg f b -> (a :-> b) -> HCxt h f a :-> b
hfree f g = run
    where run :: HCxt h f a :-> b
          run (HHole v) = g v
          run (HTerm c) = f $ hfmap run c


hcata :: forall f a. (HFunctor f) => HAlg f a -> HTerm f :-> a
hcata f = run 
    where run :: HTerm f :-> a
          run (HTerm t) = f (hfmap run t)

hcata' :: (HFunctor f) => HAlg f e -> HCxt h f e :-> e
hcata' alg = hfree alg id

-- | This function applies a whole context into another context.

appHCxt :: (HFunctor f) => HContext f (HCxt h f a) :-> HCxt h f a
appHCxt = hcata' HTerm

-- | This function lifts a many-sorted algebra to a monadic domain.
liftMHAlg :: forall m f. (Monad m, HTraversable f) =>
            HAlg f I -> HAlg f m
liftMHAlg alg =  turn . liftM alg . hmapM run
    where run :: m i -> m (I i)
          run m = do x <- m
                     return $ I x
          turn x = do I y <- x
                      return y

type HAlgM m f e = NatM m (f e) e

hfreeM :: forall f m h a b. (HTraversable f, Monad m) =>
               HAlgM m f b -> NatM m a b -> NatM m (HCxt h f a)  b
hfreeM algm var = run
    where run :: NatM m (HCxt h f a) b
          run (HHole x) = var x
          run (HTerm x) = hmapM run x >>= algm

-- | This is a monadic version of 'hcata'.

hcataM :: forall f m a. (HTraversable f, Monad m) =>
         HAlgM m f a -> NatM m (HTerm f) a
-- hcataM alg h (HTerm t) = alg =<< hmapM (hcataM alg h) t
hcataM alg = run
    where run :: NatM m (HTerm f) a
          run (HTerm x) = alg =<< hmapM run x


hcataM' :: forall m h a f. (Monad m, HTraversable f) => HAlgM m f a -> NatM m (HCxt h f a) a
-- hcataM' alg = hfreeM alg return
hcataM' f = run
    where run :: NatM m (HCxt h f a) a
          run (HHole x) = return x
          run (HTerm x) = hmapM run x >>= f

-- | This type represents context function.

type HCxtFun f g = forall a h. HCxt h f a :-> HCxt h g a

-- | This type represents uniform signature function specification.

type HSigFun f g = forall a. f a :-> g a


-- | This type represents a term algebra.

type HTermHom f g = HSigFun f (HContext g)

-- | This function applies the given term homomorphism to a
-- term/context.

appHTermHom :: (HFunctor f, HFunctor g) => HTermHom f g -> HCxtFun f g
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (HCxt h g b) -> HContext g (HCxt h g b)) -> HCxt h f b -> HCxt h g b
-- would achieve the same. The given type is chosen for clarity.
appHTermHom _ (HHole b) = HHole b
appHTermHom f (HTerm t) = appHCxt . f . hfmap (appHTermHom f) $ t

-- | This function composes two term algebras.

compHTermHom :: (HFunctor g, HFunctor h) => HTermHom g h -> HTermHom f g -> HTermHom f h
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (HCxt h g b) -> HContext g (HCxt h g b))
-- -> (a -> HCxt h f b) -> a -> HCxt h g b
-- would achieve the same. The given type is chosen for clarity.
compHTermHom f g = appHTermHom f . g

-- | This function composes a term algebra with an algebra.

compHAlg :: (HFunctor g) => HAlg g a -> HTermHom f g -> HAlg f a
compHAlg alg talg = hcata' alg . talg

-- | This function applies a signature function to the given context.

appHSigFun :: (HFunctor f, HFunctor g) => HSigFun f g -> HCxtFun f g
appHSigFun f = appHTermHom $ htermHom f


-- | This function composes two signature functions.

compHSigFun :: HSigFun g h -> HSigFun f g -> HSigFun f h
compHSigFun f g = f . g




-- | Lifts the given signature function to the canonical term homomorphism.
htermHom :: (HFunctor g) => HSigFun f g -> HTermHom f g
htermHom f = simpHCxt . f

-- | This type represents monadic context function.

type HCxtFunM m f g = forall a h. NatM m (HCxt h f a) (HCxt h g a)

-- | This type represents monadic signature functions.

type HSigFunM m f g = forall a. NatM m (f a) (g a)


-- | This type represents monadic term algebras.

type HTermHomM m f g = HSigFunM m f (HContext g)

-- | This function lifts the given signature function to a monadic
-- signature function. Note that term algebras are instances of
-- signature functions. Hence this function also applies to term
-- algebras.

hsigFunM :: (Monad m) => HSigFun f g -> HSigFunM m f g
hsigFunM f = return . f

-- | This function lifts the give monadic signature function to a
-- monadic term algebra.

htermHom' :: (HFunctor f, HFunctor g, Monad m) =>
            HSigFunM m f g -> HTermHomM m f g
htermHom' f = liftM  (HTerm . hfmap HHole) . f

-- | This function lifts the given signature function to a monadic
-- term algebra.

htermHomM :: (HFunctor g, Monad m) => HSigFun f g -> HTermHomM m f g
htermHomM f = hsigFunM $ htermHom f

-- | This function applies the given monadic term homomorphism to the
-- given term/context.

appHTermHomM :: forall f g m . (HTraversable f, HFunctor g, Monad m)
         => HTermHomM m f g -> HCxtFunM m f g
appHTermHomM f = run
    where run :: NatM m (HCxt h f a) (HCxt h g a)
          run (HHole b) = return $ HHole b
          run (HTerm t) = liftM appHCxt . (>>= f) . hmapM run $ t

-- | This function applies the given monadic signature function to the
-- given context.

appHSigFunM :: (HTraversable f, HFunctor g, Monad m) =>
                HSigFunM m f g -> HCxtFunM m f g
appHSigFunM f = appHTermHomM $ htermHom' f

-- | This function composes two monadic term algebras.

compHTermHomM :: (HTraversable g, HFunctor h, Monad m)
             => HTermHomM m g h -> HTermHomM m f g -> HTermHomM m f h
compHTermHomM f g a = g a >>= appHTermHomM f

{-| This function composes a monadic term algebra with a monadic algebra -}

compHAlgM :: (HTraversable g, Monad m) => HAlgM m g a -> HTermHomM m f g -> HAlgM m f a
compHAlgM alg talg c = hcataM' alg =<< talg c

-- | This function composes a monadic term algebra with a monadic
-- algebra.

compHAlgM' :: (HTraversable g, Monad m) => HAlgM m g a -> HTermHom f g -> HAlgM m f a
compHAlgM' alg talg = hcataM' alg . talg


{-| This function composes two monadic signature functions.  -}

compHSigFunM :: (Monad m) => HSigFunM m g h -> HSigFunM m f g -> HSigFunM m f h
compHSigFunM f g a = g a >>= f


----------------
-- Coalgebras --
----------------

type HCoalg f a = a :-> f a

{-| This function unfolds the given value to a term using the given
unravelling function. This is the unique homomorphism @a -> HTerm f@
from the given coalgebra of type @a -> f a@ to the final coalgebra
@HTerm f@. -}

hana :: forall f a. HFunctor f => HCoalg f a -> a :-> HTerm f
hana f = run
    where run :: a :-> HTerm f
          run t = HTerm $ hfmap run (f t)

type HCoalgM m f a = NatM m a (f a)

-- | This function unfolds the given value to a term using the given
-- monadic unravelling function. This is the unique homomorphism @a ->
-- HTerm f@ from the given coalgebra of type @a -> f a@ to the final
-- coalgebra @HTerm f@.

hanaM :: forall a m f. (HTraversable f, Monad m)
          => HCoalgM m f a -> NatM m a (HTerm f)
hanaM f = run 
    where run :: NatM m a (HTerm f)
          run t = liftM HTerm $ f t >>= hmapM run

--------------------------------
-- R-Algebras & Paramorphisms --
--------------------------------

-- | This type represents r-algebras over functor @f@ and with domain
-- @a@.

type HRAlg f a = f (HTerm f :*: a) :-> a

-- | This function constructs a paramorphism from the given r-algebra
hpara :: forall f a. (HFunctor f) => HRAlg f a -> HTerm f :-> a
hpara f = fsnd . hcata run
    where run :: HAlg f  (HTerm f :*: a)
          run t = HTerm (hfmap ffst t) :*: f t

-- | This type represents monadic r-algebras over monad @m@ and
-- functor @f@ and with domain @a@.
type HRAlgM m f a = NatM m (f (HTerm f :*: a)) a

-- | This function constructs a monadic paramorphism from the given
-- monadic r-algebra
hparaM :: forall f m a. (HTraversable f, Monad m) => 
         HRAlgM m f a -> NatM m(HTerm f)  a
hparaM f = liftM fsnd . hcataM run
    where run :: HAlgM m f (HTerm f :*: a)
          run t = do
            a <- f t
            return (HTerm (hfmap ffst t) :*: a)

--------------------------------
-- R-Coalgebras & Apomorphisms --
--------------------------------

-- | This type represents r-coalgebras over functor @f@ and with
-- domain @a@.
type HRCoalg f a = a :-> f (HTerm f :+: a)

-- | This function constructs an apomorphism from the given
-- r-coalgebra.
hapo :: forall f a . (HFunctor f) => HRCoalg f a -> a :-> HTerm f
hapo f = run 
    where run :: a :-> HTerm f
          run = HTerm . hfmap run' . f
          run' :: HTerm f :+: a :-> HTerm f
          run' (Inl t) = t
          run' (Inr a) = run a

-- | This type represents monadic r-coalgebras over monad @m@ and
-- functor @f@ with domain @a@.

type HRCoalgM m f a = NatM m a (f (HTerm f :+: a))

-- | This function constructs a monadic apomorphism from the given
-- monadic r-coalgebra.
hapoM :: forall f m a . (HTraversable f, Monad m) =>
        HRCoalgM m f a -> NatM m a (HTerm f)
hapoM f = run 
    where run :: NatM m a (HTerm f)
          run a = do
            t <- f a
            t' <- hmapM run' t
            return $ HTerm t'
          run' :: NatM m (HTerm f :+: a)  (HTerm f)
          run' (Inl t) = return t
          run' (Inr a) = run a

----------------------------------
-- CV-Algebras & Histomorphisms --
----------------------------------

-- $l1 For this to work we need a more general version of @:&&:@ which is of
-- kind @((* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> *@,
-- i.e. one which takes a functor as second argument instead of a
-- type.

-----------------------------------
-- CV-Coalgebras & Futumorphisms --
-----------------------------------


-- | This type represents cv-coalgebras over functor @f@ and with domain
-- @a@.

type HCVCoalg f a = a :-> f (HContext f a)


-- | This function constructs the unique futumorphism from the given
-- cv-coalgebra to the term algebra.

hfutu :: forall f a . HFunctor f => HCVCoalg f a -> a :-> HTerm f
hfutu coa = hana run . HHole
    where run :: HCoalg f (HContext f a)
          run (HHole a) = coa a
          run (HTerm v) = v


-- | This type represents monadic cv-coalgebras over monad @m@ and
-- functor @f@, and with domain @a@.

type HCVCoalgM m f a = NatM m a (f (HContext f a))

-- | This function constructs the unique monadic futumorphism from the
-- given monadic cv-coalgebra to the term algebra.
hfutuM :: forall f a m . (HTraversable f, Monad m) =>
         HCVCoalgM m f a -> NatM m a (HTerm f)
hfutuM coa = hanaM run . HHole
    where run :: HCoalgM m f (HContext f a)
          run (HHole a) = coa a
          run (HTerm v) = return v


--------------------------
-- Exponential Functors --
--------------------------

{-| Catamorphism for higher-order exponential functors. -}
hcataE :: forall f a . HExpFunctor f => HAlg f a -> HTerm f :-> a
hcataE f = cataFS . toHCxt
    where cataFS :: HExpFunctor f => HContext f a :-> a
          cataFS (HHole x) = x
          cataFS (HTerm t) = f (hxmap cataFS HHole t)


{-{-| Anamorphism for higher-order exponential functors. -}
hanaE :: forall a f . HExpFunctor f => HCoalg f a -> a :-> HTerm (f :&: a)
hanaE f = run
    where run :: a :-> HTerm (f :&: a)
          run t = HTerm $ hxmap run (snd . hprojectP . unHTerm) (f t) :&: t-}

-- | Variant of 'appHCxt' for contexts over 'HExpFunctor' signatures.
appHCxtE :: (HExpFunctor f) => HContext f (HCxt h f a) :-> HCxt h f a
appHCxtE (HHole x) = x
appHCxtE (HTerm t)  = HTerm (hxmap appHCxtE HHole t)

-- | Variant of 'appHTermHom' for term homomorphisms from and to
-- 'HExpFunctor' signatures.
appHTermHomE :: forall f g . (HExpFunctor f, HExpFunctor g) => HTermHom f g
             -> HTerm f :-> HTerm g
appHTermHomE f = cataFS . toHCxt
    where cataFS :: HContext f (HTerm g) :-> HTerm g
          cataFS (HHole x) = x
          cataFS (HTerm t) = appHCxtE (f (hxmap cataFS HHole t))