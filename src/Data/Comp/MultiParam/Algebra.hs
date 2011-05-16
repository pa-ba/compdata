{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeOperators,
  FlexibleContexts, CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Algebra
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the notion of algebras and catamorphisms, and their
-- generalizations to e.g. monadic versions and other (co)recursion schemes.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Algebra (
      -- * Algebras & Catamorphisms
      Alg,
      free,
      cata,
      cata',
      appCxt,
      
      -- * Monadic Algebras & Catamorphisms
      AlgM,
--      algM,
      freeM,
      cataM,
      AlgM',
      Compose(..),
      freeM',
      cataM',

      -- * Term Homomorphisms
      CxtFun,
      SigFun,
      TermHom,
      appTermHom,
      appTermHom',
      compTermHom,
      appSigFun,
      appSigFun',
      compSigFun,
      termHom,
      compAlg,

      -- * Monadic Term Homomorphisms
      CxtFunM,
      SigFunM,
      TermHomM,
      sigFunM,
      termHom',
      appTermHomM,
      appTermHomM',
      termHomM,
      appSigFunM,
      appSigFunM',
      compTermHomM,
      compSigFunM,
      compAlgM,
      compAlgM'
    ) where

import Prelude hiding (sequence, mapM)
import Control.Monad hiding (sequence, mapM)
import Data.Functor.Compose -- Functor composition
import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.HDitraversable

import Unsafe.Coerce (unsafeCoerce)

{-| This type represents an algebra over a difunctor @f@ and carrier @a@. -}
type Alg f a = f a a :-> a

{-| Construct a catamorphism for contexts over @f@ with holes of type @b@, from
  the given algebra. -}
free :: forall h f a b. HDifunctor f
        => Alg f a -> (b :-> a) -> Cxt h f a b :-> a
free f g = run
    where run :: Cxt h f a b :-> a
          run (Term t) = f (hfmap run t)
          run (Hole x) = g x
          run (Place p) = p

{-| Construct a catamorphism from the given algebra. -}
cata :: forall f a. HDifunctor f => Alg f a -> Term f :-> a 
{-# NOINLINE [1] cata #-}
cata f = run . coerceCxt
    where run :: Trm f a :-> a
          run (Term t) = f (hfmap run t)
          run (Place x) = x

{-| A generalisation of 'cata' from terms over @f@ to contexts over @f@, where
  the holes have the type of the algebra carrier. -}
cata' :: HDifunctor f => Alg f a -> Cxt h f a a :-> a
{-# INLINE cata' #-}
cata' f = free f id

{-| This function applies a whole context into another context. -}
appCxt :: HDifunctor f => Cxt Hole f a (Cxt h f a b) :-> Cxt h f a b
appCxt (Term t) = Term (hfmap appCxt t)
appCxt (Hole x) = x
appCxt (Place p) = Place p

{-| This type represents a monadic algebra. It is similar to 'Alg' but
  the return type is monadic. -}
type AlgM m f a = NatM m (f a a) a

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @b@, from the given monadic algebra. -}
freeM :: forall m h f a b. (HDitraversable f m a, Monad m)
         => AlgM m f a -> NatM m b a -> NatM m (Cxt h f a b) a
freeM f g = run
    where run :: NatM m (Cxt h f a b) a
          run (Term t) = f =<< hdimapM run t
          run (Hole x) = g x
          run (Place p) = return p

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM :: forall m f a. (HDitraversable f m a, Monad m)
         => AlgM m f a -> NatM m (Term f) a
{-# NOINLINE [1] cataM #-}
cataM algm = run . coerceCxt
    where run :: NatM m (Trm f a) a
          run (Term t) = algm =<< hdimapM run t
          run (Place x) = return x

{-| This type represents a monadic algebra, but where the covariant argument is
  also a monadic computation. -}
type AlgM' m f a = NatM m (f a (Compose m a)) a

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @b@, from the given monadic algebra. -}
freeM' :: forall m h f a b. (HDifunctor f, Monad m)
          => AlgM' m f a -> NatM m b a -> NatM m (Cxt h f a b) a
freeM' f g = run
    where run :: NatM m (Cxt h f a b) a
          run (Term t) = f $ hfmap (Compose . run) t
          run (Hole x) = g x
          run (Place p) = return p

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM' :: forall m f a. (HDifunctor f, Monad m)
          => AlgM' m f a -> NatM m (Term f) a
{-# NOINLINE [1] cataM' #-}
cataM' algm = run . coerceCxt
    where run :: NatM m (Trm f a) a
          run (Term t) = algm $ hfmap (Compose . run) t
          run (Place x) = return x

{-| This type represents a signature function. -}
type SigFun f g = forall a b. f a b :-> g a b

{-| This type represents a context function. -}
type CxtFun f g = forall h. SigFun (Cxt h f) (Cxt h g)

{-| This type represents a term homomorphism. -}
type TermHom f g = SigFun f (Context g)

{-| Apply a term homomorphism recursively to a term/context. -}
appTermHom :: forall f g. (HDifunctor f, HDifunctor g)
              => TermHom f g -> CxtFun f g
{-# INLINE [1] appTermHom #-}
appTermHom f = run where
    run :: CxtFun f g
    run (Term t) = appCxt (f (hfmap run t))
    run (Hole x) = Hole x
    run (Place p) = Place p

-- | Apply a term homomorphism recursively to a term/context. This is
-- a top-down variant of 'appTermHom'.
appTermHom' :: forall f g. (HDifunctor g)
              => TermHom f g -> CxtFun f g
{-# INLINE [1] appTermHom' #-}
appTermHom' f = run where
    run :: CxtFun f g
    run (Term t) = appCxt (hfmapCxt run (f t))
    run (Hole x) = Hole x
    run (Place p) = Place p

{-| Compose two term homomorphisms. -}
compTermHom :: (HDifunctor g, HDifunctor h)
               => TermHom g h -> TermHom f g -> TermHom f h
compTermHom f g = appTermHom f . g

{-| Compose an algebra with a term homomorphism to get a new algebra. -}
compAlg :: (HDifunctor f, HDifunctor g) => Alg g a -> TermHom f g -> Alg f a
compAlg alg talg = cata' alg . talg

{-| This function applies a signature function to the given context. -}
appSigFun :: forall f g. (HDifunctor f) => SigFun f g -> CxtFun f g
appSigFun f = run where
    run :: CxtFun f g
    run (Term t) = Term (f (hfmap run t))
    run (Hole x) = Hole x
    run (Place p) = Place p

{-| This function applies a signature function to the given context. -}
appSigFun' :: forall f g. (HDifunctor g) => SigFun f g -> CxtFun f g
appSigFun' f = run where
    run :: CxtFun f g
    run (Term t) = Term (hfmap run (f t))
    run (Hole x) = Hole x
    run (Place p) = Place p

{-| This function composes two signature functions. -}
compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g

{-| Lifts the given signature function to the canonical term homomorphism. -}
termHom :: HDifunctor g => SigFun f g -> TermHom f g
termHom f = simpCxt . f

{-| This type represents a monadic signature function. -}
type SigFunM m f g = forall a b. NatM m (f a b) (g a b)

{-| This type represents a monadic context function. -}
type CxtFunM m f g = forall h . SigFunM m (Cxt h f) (Cxt h g)

{-| This type represents a monadic context function. -}
type CxtFunM' m f g = forall h b . NatM m (Cxt h f Any b) (Cxt h g Any b)


coerceCxtFunM :: CxtFunM' m f g -> CxtFunM m f g
coerceCxtFunM = unsafeCoerce


{-| This type represents a monadic term homomorphism. -}
type TermHomM m f g = SigFunM m f (Cxt Hole g)


{-| Lift the given signature function to a monadic signature function. Note that
  term homomorphisms are instances of signature functions. Hence this function
  also applies to term homomorphisms. -}
sigFunM :: Monad m => SigFun f g -> SigFunM m f g
sigFunM f = return . f

{-| Lift the give monadic signature function to a monadic term homomorphism. -}
termHom' :: (HDifunctor f, HDifunctor g, Monad m)
            => SigFunM m f g -> TermHomM m f g
termHom' f = liftM  (Term . hfmap Hole) . f

{-| Lift the given signature function to a monadic term homomorphism. -}
termHomM :: (HDifunctor g, Monad m) => SigFun f g -> TermHomM m f g
termHomM f = sigFunM $ termHom f

{-| Apply a monadic term homomorphism recursively to a term/context. -}
appTermHomM :: forall f g m. (HDitraversable f m Any, HDifunctor g, Monad m)
               => TermHomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appTermHomM #-}
appTermHomM f = coerceCxtFunM run
    where run :: CxtFunM' m f g
          run (Term t) = liftM appCxt (f =<< hdimapM run t)
          run (Hole x) = return (Hole x)
          run (Place p) = return (Place p)

-- | Apply a monadic term homomorphism recursively to a
-- term/context. This is a top-down variant of 'appTermHomM'.
appTermHomM' :: forall f g m. (HDitraversable g m Any, Monad m)
               => TermHomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appTermHomM' #-}
appTermHomM' f = coerceCxtFunM run
    where run :: CxtFunM' m f g
          run (Term t) = liftM appCxt (hdimapMCxt run =<<  f t)
          run (Hole x) = return (Hole x)
          run (Place p) = return (Place p)


{-| This function applies a monadic signature function to the given context. -}
appSigFunM :: forall m f g. (HDitraversable f m Any, Monad m)
              => SigFunM m f g -> CxtFunM m f g
appSigFunM f = coerceCxtFunM run
    where run :: CxtFunM' m f g
          run (Term t) = liftM Term (f =<< hdimapM run t)
          run (Hole x) = return (Hole x)
          run (Place p) = return (Place p)

-- | This function applies a monadic signature function to the given
-- context. This is a top-down variant of 'appSigFunM'.
appSigFunM' :: forall m f g. (HDitraversable g m Any, Monad m)
              => SigFunM m f g -> CxtFunM m f g
appSigFunM' f = coerceCxtFunM run
    where run :: CxtFunM' m f g
          run (Term t) = liftM Term (hdimapM run =<< f t)
          run (Hole x) = return (Hole x)
          run (Place p) = return (Place p)


{-| Compose two monadic term homomorphisms. -}
compTermHomM :: (HDitraversable g m Any, HDifunctor h, Monad m)
                => TermHomM m g h -> TermHomM m f g -> TermHomM m f h
compTermHomM f g = appTermHomM f <=< g

{-| Compose a monadic algebra with a monadic term homomorphism to get a new
  monadic algebra. -}
compAlgM :: (HDitraversable g m a, Monad m)
            => AlgM m g a -> TermHomM m f g -> AlgM m f a
compAlgM alg talg = freeM alg return <=< talg

{-| Compose a monadic algebra with a term homomorphism to get a new monadic
  algebra. -}
compAlgM' :: (HDitraversable g m a, Monad m) => AlgM m g a
          -> TermHom f g -> AlgM m f a
compAlgM' alg talg = freeM alg return . talg

{-| This function composes two monadic signature functions. -}
compSigFunM :: Monad m => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g a = g a >>= f


#ifndef NO_RULES
{-# RULES
  "cata/appTermHom" forall (a :: Alg g d) (h :: TermHom f g) x.
    cata a (appTermHom h x) = cata (compAlg a h) x;

  "appTermHom/appTermHom" forall (a :: TermHom g h) (h :: TermHom f g) x.
    appTermHom a (appTermHom h x) = appTermHom (compTermHom a h) x;
 #-}

{-
{-# RULES 
  "cataM/appTermHomM" forall (a :: AlgM m g d) (h :: TermHomM m f g d) x.
     appTermHomM h x >>= cataM a = cataM (compAlgM a h) x;

  "cataM/appTermHom" forall (a :: AlgM m g d) (h :: TermHom f g) x.
     cataM a (appTermHom h x) = cataM (compAlgM' a h) x;

  "appTermHomM/appTermHomM" forall (a :: TermHomM m g h b) (h :: TermHomM m f g b) x.
    appTermHomM h x >>= appTermHomM a = appTermHomM (compTermHomM a h) x;
 #-}

{-# RULES
  "cata/build"  forall alg (g :: forall a . Alg f a -> a) .
                cata alg (build g) = g alg
 #-}
-}
#endif