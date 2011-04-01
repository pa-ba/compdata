{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeOperators, CPP,
  FlexibleContexts #-}
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

module Data.Comp.Param.Algebra (
      -- * Algebras & Catamorphisms
      Alg,
      free,
      cata,
      cata',
      appCxt,
      
      -- * Monadic Algebras & Catamorphisms
      AlgM,
      algM,
      freeM,
      cataM,
      cataM',

      -- * Term Homomorphisms
      (:<)(..),
      CxtFun,
      SigFun,
      TermHom,
      appTermHom,
      compTermHom,
      appSigFun,
      compSigFun,
      termHom,
      compAlg,
--      compCoalg,
--      compCVCoalg,

      -- * Monadic Term Homomorphisms
      CxtFunM,
      SigFunM,
      TermHomM,
      SigFunM',
      TermHomM',
      sigFunM,
      termHom',
      appTermHomM,
      termHomM,
      termHomM',
      appSigFunM,
      appSigFunM',
      compTermHomM,
      compSigFunM,
      compAlgM,
      compAlgM',

      -- * Coalgebras & Anamorphisms
      Coalg,
      ana,
--      ana',
      CoalgM,
      anaM,

      -- * R-Algebras & Paramorphisms
      RAlg,
      para,
      RAlgM,
      paraM,
{-
      -- * R-Coalgebras & Apomorphisms
      RCoalg,
      apo,
      RCoalgM,
      apoM,
-}
      -- * CV-Algebras & Histomorphisms
      CVAlg,
      histo,
      CVAlgM,
      histoM,

      -- * CV-Coalgebras & Futumorphisms
      CVCoalg,
      futu,
      CVCoalg',
      futu',
      CVCoalgM,
      futuM
    ) where

import Prelude hiding (sequence, mapM)
import Control.Monad hiding (sequence, mapM)
import Data.Comp.Param.Term
import Data.Comp.Param.Sub
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable

{-| This type represents an algebra over a difunctor @f@ and carrier @a@. -}
type Alg f a = f a a -> a

{-| Construct a catamorphism for contexts over @f@ with holes of type @a@, from
  the given algebra. -}
free :: forall f a b c. Difunctor f
     => (f a c -> c) -> (b -> c) -> Cxt f a b -> c
free f g = run
    where run :: Cxt f a b -> c
          run (Hole x) = g x
          run (Term t) = f (fmap run t)

{-| Construct a catamorphism from the given algebra. -}
cata :: forall f a. Difunctor f => Alg f a -> Term f -> a 
{-# NOINLINE [1] cata #-}
cata f = run . toCxt
    where run :: Cxt f a a -> a
          run (Term t) = f (fmap run t)
          run (Hole x) = x

{-| A generalisation of 'cata' from terms over @f@ to contexts over @f@, where
  the holes have the type of the algebra carrier. -}
cata' :: Difunctor f => Alg f a -> Cxt f a a -> a
{-# INLINE cata' #-}
cata' f = free f id

{-| This function applies a whole context into another context. -}
appCxt :: Difunctor f => Cxt f a (Cxt f a b) -> Cxt f a b
appCxt (Hole x) = x
appCxt (Term t) = Term (fmap appCxt t)

{-| This type represents a monadic algebra. It is similar to 'Alg' but
  the return type is monadic. -}
type AlgM m f a = f a a -> m a

{-| Convert a monadic algebra into an ordinary algebra with a monadic
  carrier. -}
algM :: (Ditraversable f m a, Monad m) => AlgM m f a -> Alg f (m a)
algM f x = disequence (dimap return id x) >>= f

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @b@, from the given monadic algebra. -}
freeM :: forall m f a b c. (Ditraversable f m a, Monad m)
      => (f a c -> m c) -> (b -> m c) -> Cxt f a b -> m c
freeM f g = run
    where run :: Cxt f a b -> m c
          run (Hole x) = g x
          run (Term t) = f =<< dimapM run t

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM :: (Ditraversable f m a, Monad m) => AlgM m f a -> Term f -> m a
{-# NOINLINE [1] cataM #-}
cataM f = freeM f return . toCxt

{-| A generalisation of 'cataM' from terms over @f@ to contexts over @f@, where
  the holes have the type of the monadic algebra carrier. -}
cataM' :: forall m f a. (Ditraversable f m a, Monad m)
       => AlgM m f a -> Cxt f a (m a) -> m a
{-# NOINLINE [1] cataM' #-}
cataM' f = freeM f id

{-| This type represents a context function. -}
type CxtFun f g = forall a b. (a :< b) => Cxt f a b -> Cxt g a b

{-| This type represents a signature function. -}
type SigFun f g = forall a b. (a :< b) => f a b -> g a b

{-| This type represents a term homomorphism. -}
type TermHom f g = SigFun f (Cxt g)

{-| Apply a term homomorphism recursively to a term/context. -}
appTermHom :: forall f g. (Difunctor f, Difunctor g)
           => TermHom f g -> CxtFun f g
{-# INLINE [1] appTermHom #-}
appTermHom f = free (appCxt . f) Hole

{-| Compose two term homomorphisms. -}
compTermHom :: (Difunctor g, Difunctor h)
            => TermHom g h -> TermHom f g -> TermHom f h
compTermHom f g = appTermHom f . g

{-| Compose an algebra with a term homomorphism to get a new algebra. -}
compAlg :: (Difunctor f, Difunctor g) => Alg g a -> TermHom f g -> Alg f a
compAlg alg talg = cata' alg . talg

{-
{-| Compose a term homomorphism with a coalgebra to get a cv-coalgebra. -}
compCoalg :: TermHom f g -> Coalg f a -> CVCoalg' g a
compCoalg hom coa = hom . coa

{-| Compose a term homomorphism with a cv-coalgebra to get a new cv-coalgebra.
 -}
compCVCoalg :: (Functor f, Functor g)
  => TermHom f g -> CVCoalg' f a -> CVCoalg' g a
compCVCoalg hom coa = appTermHom' hom . coa

-}

{-| This function applies a signature function to the given context. -}
appSigFun :: forall f g. (Difunctor f, Difunctor g) => SigFun f g -> CxtFun f g
appSigFun f = appTermHom $ termHom f

{-| This function composes two signature functions. -}
compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g

{-| Lifts the given signature function to the canonical term homomorphism. -}
termHom :: Difunctor g => SigFun f g -> TermHom f g
termHom f = simpCxt . f

{-| This type represents a monadic context function. -}
type CxtFunM m f g a = forall b. (a :< b) => Cxt f a b -> m (Cxt g a b)

{-| This type represents a monadic signature function. -}
type SigFunM m f g a = forall b. (a :< b) => f a b -> m (g a b)

{-| This type represents a monadic signature function. It is similar to
  'SigFunM' but has monadic values also in the domain. -}
type SigFunM' m f g a = forall b. (a :< b) => f a (m b) -> m (g a b)

{-| This type represents a monadic term homomorphism. -}
type TermHomM m f g a = SigFunM m f (Cxt g) a

{-| This type represents a monadic term homomorphism. It is similar to
  'TermHomM' but has monadic values also in the domain. -}
type TermHomM' m f g a = SigFunM' m f (Cxt g) a

{-| Lift the given signature function to a monadic signature function. Note that
  term homomorphisms are instances of signature functions. Hence this function
  also applies to term homomorphisms. -}
sigFunM :: Monad m => SigFun f g -> SigFunM m f g a
sigFunM f = return . f

{-| Lift the give monadic signature function to a monadic term homomorphism. -}
termHom' :: (Difunctor f, Difunctor g, Monad m)
         => SigFunM m f g a -> TermHomM m f g a
termHom' f = liftM  (Term . fmap Hole) . f

{-| Lift the given signature function to a monadic term homomorphism. -}
termHomM :: (Difunctor g, Monad m) => SigFun f g -> TermHomM m f g a
termHomM f = sigFunM $ termHom f

{-| Apply a monadic term homomorphism recursively to a term/context. -}
appTermHomM :: forall f g m a. (Ditraversable f m a, Difunctor g, Monad m)
            => TermHomM m f g a -> CxtFunM m f g a
{-# NOINLINE [1] appTermHomM #-}
appTermHomM f = run
    where run :: CxtFunM m f g a
          run (Hole x) = return (Hole x)
          run (Term t) = liftM appCxt (f =<< dimapM run t)

{-| This function constructs the unique monadic homomorphism from the
  initial term algebra to the given term algebra. -}
termHomM' :: forall f g m a. (Difunctor f, Difunctor g, Monad m)
          => TermHomM' m f g a -> CxtFunM m f g a
termHomM' f = run 
    where run :: CxtFunM m f g a
          run (Hole x) = return (Hole x)
          run (Term t) = liftM appCxt (f (fmap run t))

{-| This function applies a monadic signature function to the given context. -}
appSigFunM :: (Ditraversable f m a, Difunctor g, Monad m)
           => SigFunM m f g a -> CxtFunM m f g a
appSigFunM f = appTermHomM $ termHom' f

{-| This function applies a signature function to the given context. -}
appSigFunM' :: forall f g m a. (Ditraversable f m a, Difunctor g, Monad m)
            => SigFunM' m f g a -> CxtFunM m f g a
appSigFunM' f = run 
    where run :: CxtFunM m f g a
          run (Hole x) = return (Hole x)
          run (Term t) = liftM Term (f (fmap run t))

{-| Compose two monadic term homomorphisms. -}
compTermHomM :: (Ditraversable g m a, Difunctor h, Monad m)
             => TermHomM m g h a -> TermHomM m f g a -> TermHomM m f h a
compTermHomM f g = appTermHomM f <=< g

{-| Compose a monadic algebra with a monadic term homomorphism to get a new
  monadic algebra. -}
compAlgM :: (Ditraversable g m a, Monad m)
         => AlgM m g a -> TermHomM m f g a -> AlgM m f a
compAlgM alg talg = freeM alg return <=< talg

{-| Compose a monadic algebra with a term homomorphism to get a new monadic
  algebra. -}
compAlgM' :: (Ditraversable g m a, Monad m) => AlgM m g a
          -> TermHom f g -> AlgM m f a
compAlgM' alg talg = freeM alg return . talg

{-| This function composes two monadic signature functions. -}
compSigFunM :: Monad m => SigFunM m g h a -> SigFunM m f g a -> SigFunM m f h a
compSigFunM f g a = g a >>= f


----------------
-- Coalgebras --
----------------

-- |Constant difunctor.
data K b a e = K b

{-| This type represents a coalgebra over a difunctor @f@ and carrier @a@. The
 list of @b@s represent the free variables that may occur in the constructed
 value. Such variables are injected via the @K@ functor. If @f@ is itself a
 binder, then the variables bound by @f@ can be passed to the covariant
 argument, thereby making them available to subterms. -}
type Coalg f a = forall b. (a,[b]) -> (K b :+: f) b (a,[b])

{-| Construct an anamorphism from the given coalgebra. -}
ana :: forall a f. Difunctor f => Coalg f a -> a -> Term f
ana f x = run (x,[]) -- initially, the set of available parameters is empty
    where run :: (a,[b]) -> Cxt f b b
          run a = case f a of
                    Inl (K x) -> Hole x
                    Inr t -> Term $ fmap run t

{-| This type represents a monadic coalgebra over a difunctor @f@ and carrier
  @a@. -}
type CoalgM m f a = forall b. (a,[b]) -> m ((K b :+: f) b (a,[b]))

{-| Construct a monadic anamorphism from the given monadic coalgebra. -}
anaM :: forall a m f. (Ditraversable f m Nothing, Monad m)
     => CoalgM m f a -> a -> m (Term f)
anaM f x = run (x,[])
    where run :: Ditraversable f m b => (a,[b]) -> m (Cxt f b b)
          run a = do a' <- f a
                     case a' of
                       Inl (K x) -> return (Hole x)
                       Inr t -> liftM Term $ dimapM run t

--------------------------------
-- R-Algebras & Paramorphisms --
--------------------------------

{-| This type represents an r-algebra over a difunctor @f@ and carrier @a@. -}
type RAlg f a = f a (Cxt f a a, a) -> a

{-| Construct a paramorphism from the given r-algebra. -}
para :: forall f a. Difunctor f => RAlg f a -> Term f -> a
para f = run . toCxt
    where run :: Cxt f a a -> a
          run (Hole x) = x
          run (Term t) = f $ fmap (\x -> (x, run x)) t

{-| This type represents a monadic r-algebra over a difunctor @f@ and carrier
  @a@. -}
type RAlgM m f a = f a (Cxt f a a, a) -> m a
{-| Construct a monadic paramorphism from the given monadic r-algebra. -}
paraM :: forall m f a. (Ditraversable f m a, Monad m) => 
         RAlgM m f a -> Term f -> m a
paraM f = run . toCxt
    where run :: Cxt f a a -> m a
          run (Hole x) = return x
          run (Term t) = f =<< dimapM (\x -> run x >>= \y -> return (x, y)) t


--------------------------------
-- R-Coalgebras & Apomorphisms --
--------------------------------
{-
{-| This type represents an r-coalgebra over a difunctor @f@ and carrier @a@. -}
type RCoalg f a = forall b. (a,[b]) -> (K b :+: f) b (Either (Cxt f a a) (a,[b]))

{-| Construct an apomorphism from the given r-coalgebra. -}
apo :: (Functor f) => RCoalg f a -> a -> Term f
apo f = run 
    where run = Term . fmap run' . f
          run' (Left t) = t
          run' (Right a) = run a
-- can also be defined in terms of anamorphisms (but less
-- efficiently):
-- apo f = ana run . Right
--     where run (Left (Term t)) = fmap Left t
--           run (Right a) = f a

{-| This type represents a monadic r-coalgebra over a functor @f@ and carrier
  @a@. -}
type RCoalgM m f a = a -> m (f (Either (Term f) a))

{-| Construct a monadic apomorphism from the given monadic r-coalgebra. -}
apoM :: (Traversable f, Monad m) =>
        RCoalgM m f a -> a -> m (Term f)
apoM f = run 
    where run a = do
            t <- f a
            t' <- mapM run' t
            return $ Term t'
          run' (Left t) = return t
          run' (Right a) = run a

-- can also be defined in terms of anamorphisms (but less
-- efficiently):
-- apoM f = anaM run . Right
--     where run (Left (Term t)) = return $ fmap Left t
--           run (Right a) = f a

-}
----------------------------------
-- CV-Algebras & Histomorphisms --
----------------------------------

{-| This type represents a cv-algebra over a difunctor @f@ and carrier @a@. -}
type CVAlg f a f' = f a (Cxt f' a a) -> a

-- | This function applies 'projectP' at the tip of the term.
projectTip  :: DistProd f a f' => Cxt f' b a -> a
projectTip (Hole x) = x
projectTip (Term v) = snd $ projectP v

{-| Construct a histomorphism from the given cv-algebra. -}
histo :: (Difunctor f, DistProd f a f') => CVAlg f a f' -> Term f -> a
histo alg = projectTip . free run Hole . toCxt
    where run v = Term $ injectP (alg v) v

{-| This type represents a monadic cv-algebra over a functor @f@ and carrier
  @a@. -}
type CVAlgM m f a f' = f a (Cxt f' a a) -> m a

{-| Construct a monadic histomorphism from the given monadic cv-algebra. -}
histoM :: (Ditraversable f m a, Monad m, DistProd f a f') =>
          CVAlgM m f a f' -> Term f -> m a
histoM alg = liftM projectTip . freeM run (return . Hole) . toCxt
    where run v = do r <- alg v
                     return $ Term $ injectP r v

-----------------------------------
-- CV-Coalgebras & Futumorphisms --
-----------------------------------

{-| This type represents a cv-coalgebra over a difunctor @f@ and carrier @a@.
 The list of @b@s represent the free variables that may occur in the constructed
 value. Such variables are injected via the @K@ functor. If @f@ is itself a
 binder, then the variables bound by @f@ can be passed to the covariant
 argument, thereby making them available to subterms. -}
type CVCoalg f a = forall b. (a,[b]) -> (K b :+: f) b (Cxt (K b :+: f) b (a,[b]))

{-| Construct a futumorphism from the given cv-coalgebra. -}
futu :: forall f a. Difunctor f => CVCoalg f a -> a -> Term f
futu coa x = run $ Hole (x,[])
    where run :: Cxt (K b :+: f) b (a,[b]) -> Cxt f b b
          run (Hole x) = run' (coa x)
          run (Term t) = run' t
          run' :: (K b :+: f) b (Cxt (K b :+: f) b (a,[b])) -> Cxt f b b
          run' (Inl (K x)) = Hole x
          run' (Inr t) = Term $ fmap run t

{-| This type represents a monadic cv-coalgebra over a difunctor @f@ and carrier
  @a@. -}
type CVCoalgM m f a = forall b. (a,[b]) -> m ((K b :+: f) b (Cxt (K b :+: f) b (a,[b])))

{-| Construct a monadic futumorphism from the given monadic cv-coalgebra. -}
futuM :: forall f a m. (Ditraversable f m Nothing, Monad m) =>
         CVCoalgM m f a -> a -> m (Term f)
futuM coa x = run $ Hole (x,[])
    where run :: Ditraversable f m b
               => Cxt (K b :+: f) b (a,[b]) -> m (Cxt f b b)
          run (Hole x) = coa x >>= run'
          run (Term t) = run' t
          run' :: Ditraversable f m b
               => (K b :+: f) b (Cxt (K b :+: f) b (a,[b])) -> m (Cxt f b b)
          run' (Inl (K x)) = return $ Hole x
          run' (Inr t) = liftM Term $ dimapM run t

{-| This type represents a generalised cv-coalgebra over a difunctor @f@ and
  carrier @a@. -}
type CVCoalg' f a = forall b. (a,[b]) -> Cxt (K b :+: f) b (a,[b])

{-| Construct a futumorphism from the given generalised cv-coalgebra. -}
futu' :: forall f a. Difunctor f => CVCoalg' f a -> a -> Term f
futu' coa x = run $ Hole (x,[])
    where run :: Cxt (K b :+: f) b (a,[b]) -> Cxt f b b
          run (Hole x) = run (coa x)
          run (Term t) = run' t
          run' :: (K b :+: f) b (Cxt (K b :+: f) b (a,[b])) -> Cxt f b b
          run' (Inl (K x)) = Hole x
          run' (Inr t) = Term $ fmap run t


-------------------
-- rewrite rules --
-------------------

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