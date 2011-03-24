{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeOperators,
  FlexibleContexts, CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Algebra
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
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
      CxtFun,
      SigFun,
      TermHom,
      appTermHom,
--      compTermHom,
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
--      termHomM,
      termHomM',
      appSigFunM,
      appSigFunM',
--      compTermHomM,
      compSigFunM,
      compAlgM,
--      compAlgM',

{-      -- * Coalgebras & Anamorphisms
      Coalg,
      ana,
      ana',
      CoalgM,
      anaM,

      -- * R-Algebras & Paramorphisms
      RAlg,
      para,
      RAlgM,
      paraM,

      -- * R-Coalgebras & Apomorphisms
      RCoalg,
      apo,
      RCoalgM,
      apoM,

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
      futuM-}
    ) where

import Prelude hiding (sequence, mapM)
import Control.Monad hiding (sequence, mapM)
import Data.Comp.Param.Term
import Data.Comp.Param.Functor
import Data.Comp.Param.Traversable

{-| This type represents an algebra over a functor @f@ and carrier @a@. -}
type Alg f a = f a a -> a

{-| Construct a catamorphism for contexts over @f@ with holes of type @a@, from
  the given algebra. -}
free :: forall f h b a . Difunctor f => (f a b -> b) -> (a -> b) -> Cxt f a a -> b
free f g = run
    where run :: Cxt f a a -> b
          run (Hole x) = g x
          run (Term t) = f (fmap run t)

{-| Construct a catamorphism from the given algebra. -}
cata :: forall f a . Difunctor f => Alg f a -> Term f -> a 
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
-- appCxt = cata' Term
appCxt (Hole x) = x
appCxt (Term t) = Term (fmap appCxt t)



{-| This type represents a monadic algebra. It is similar to 'Alg' but
the return type is monadic.  -}

type AlgM m f a = f a (m a) -> m a


{-| Convert a monadic algebra into an ordinary algebra with a monadic
  carrier. -}
algM :: (Difunctor f, Monad m) => AlgM m f a -> Alg f (m a)
algM f x = f $ dimap return id x


{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @a@, from the given monadic algebra. -}
freeM :: forall h f a m b. (Difunctor f, Monad m) =>
         AlgM m f b -> (a -> m b) -> Cxt f b a -> m b
freeM f g = run
    where run :: Cxt f b a -> m b
          run (Hole x) = g x
          run (Term t) = f (fmap run t)

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM :: (Difunctor f, Monad m) => AlgM m f a -> Term f -> m a
cataM f = free f return . toCxt

{-| A generalisation of 'cataM' from terms over @f@ to contexts over @f@, where
  the holes have the type of the monadic algebra carrier. -}
cataM' :: forall h f a m . (Difunctor f, Monad m)
          => AlgM m f a -> Cxt f a (m a) -> m a
cataM' f = freeM f id

{-| This type represents a context function. -}
type CxtFun f g = forall a b. (a :< b) => Cxt f a b -> Cxt g a b

{-| This type represents a signature function.-}
type SigFun f g = forall a b. (a :< b) => f a b -> g a b

{-| This type represents a term homomorphism. -}
--type TermHom f g = forall a h. f a (Cxt h a a) -> Cxt g a (Cxt h a a) -- SigFun f (Context g)
type TermHom f g = SigFun f (Cxt g) --f a b -> Cxt g a b -- SigFun f (Context g)

{-| Apply a term homomorphism recursively to a term/context. -}
appTermHom :: forall f g. (Difunctor f, Difunctor g)
           => TermHom f g -> CxtFun f g
appTermHom f = run where
    run :: CxtFun f g
    run (Hole x) = Hole x
    run (Term t) = appCxt (f (fmap run t))


{-| Compose two term homomorphisms. -}
compTermHom :: (Difunctor g, Difunctor h) => TermHom g h -> TermHom f g -> TermHom f h
compTermHom f g = appTermHom f . g {- run . g
    where run :: Cxt g a (Cxt h' a a) -> Cxt h a (Cxt h' a a)
          run (Hole x) = Hole x
          run (Term (t :: g a (Cxt g a (Cxt h' a a)))) = Term (f (fmap run t :: g a (Cxt h a (Cxt h' a a))))-}

{-| Compose an algebra with a term homomorphism to get a new algebra. -}
compAlg :: (Difunctor f, Difunctor g) => Alg g a -> TermHom f g -> Alg f a
compAlg alg talg = cata' alg . talg
--compAlg alg talg = cata' alg . appCxt . talg . fmap Hole

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
{-appSigFun f = run --appTermHom $ termHom f
    where run :: CxtFun f g
          run (Hole x) = Hole x
          run (Term t) = Term $ f (fmap run t)-}

{-| This function composes two signature functions. -}
compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g


{-| Lifts the given signature function to the canonical term homomorphism. -}
termHom :: Difunctor g => SigFun f g -> TermHom f g
termHom f = simpCxt . f

{-|
  This type represents a monadic context function.
-}
type CxtFunM m f g = forall a b. (a :< b) => Cxt f a b -> m (Cxt g a b)
--type CxtFunM m f g = forall a. Cxt f a a -> m (Cxt g a a)

{-| This type represents a monadic signature function. -}
type SigFunM m f g = forall a b. (a :< b) => f a b -> m (g a b)
--type SigFunM m f g = forall a e. f a e -> m (g a e)

{-| This type represents a monadic signature function.  It is similar
to 'SigFunM' but has monadic values also in the domain. -}
type SigFunM' m f g = forall a b. (a :< b) => f a (m b) -> m (g a b)

{-| This type represents a monadic term homomorphism.  -}
type TermHomM m f g = SigFunM m f (Cxt g)

{-| This type represents a monadic term homomorphism. It is similar to
'TermHomM' but has monadic values also in the domain. -}
type TermHomM' m f g = SigFunM' m f (Cxt g)

{-| Lift the given signature function to a monadic signature function. Note that
  term homomorphisms are instances of signature functions. Hence this function
  also applies to term homomorphisms. -}
sigFunM :: Monad m => SigFun f g -> SigFunM m f g
sigFunM f = return . f

{-| Lift the give monadic signature function to a monadic term homomorphism. -}
termHom' :: (Difunctor f, Difunctor g, Monad m) => SigFunM m f g -> TermHomM m f g
termHom' f = liftM  (Term . fmap Hole) . f

{-{-| Lift the given signature function to a monadic term homomorphism. -}
termHomM :: (Difunctor g, Monad m) => SigFun f g -> TermHomM m f g
termHomM f = sigFunM $ termHom f
-}
{-| Apply a monadic term homomorphism recursively to a term/context. -}
appTermHomM :: forall f g m . (Ditraversable f, Difunctor g, Monad m)
            => TermHomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appTermHomM #-}
appTermHomM f = run
    where run :: CxtFunM m f g
          run (Hole x) = return (Hole x)
          run (Term t) = liftM appCxt (f =<< dimapM run t)

{-| This function constructs the unique monadic homomorphism from the
initial term algebra to the given term algebra. -}
termHomM' :: forall f g m . (Difunctor f, Difunctor g, Monad m)
          => TermHomM' m f g -> CxtFunM m f g
termHomM' f = run 
    where run :: CxtFunM m f g
          run (Hole x) = return (Hole x)
          run (Term t) = liftM appCxt (f (fmap run t))


{-| This function applies a monadic signature function to the given context. -}
appSigFunM :: (Ditraversable f, Difunctor g, Monad m) => SigFunM m f g -> CxtFunM m f g
appSigFunM f = appTermHomM $ termHom' f

{-| This function applies a signature function to the given context. -}
appSigFunM' :: forall f g m . (Ditraversable f, Difunctor g, Monad m)
              => SigFunM' m f g -> CxtFunM m f g
appSigFunM' f = run 
    where run :: CxtFunM m f g
          run (Hole x) = return (Hole x)
          run (Term t) = liftM Term (f (fmap run t))

{-{-| Compose two monadic term homomorphisms. -}
compTermHomM :: (Ditraversable g, Difunctor h, Monad m)
             => TermHomM m g h -> TermHomM m f g -> TermHomM m f h
compTermHomM f g = appTermHomM f <=< g-}

{-| Compose a monadic algebra with a monadic term homomorphism to get a new
  monadic algebra. -}
compAlgM :: (Ditraversable g, Monad m) => AlgM m g a -> TermHomM m f g -> AlgM m f a
compAlgM alg talg = cataM' alg <=< talg

{-{-| Compose a monadic algebra with a term homomorphism to get a new monadic
  algebra. -}
compAlgM' :: (Ditraversable g, Monad m) => AlgM m g a -> TermHom f g -> AlgM m f a
compAlgM' alg talg = cataM' alg . talg-}

{-| This function composes two monadic signature functions.  -}
compSigFunM :: (Monad m) => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g a = g a >>= f

{-
----------------
-- Coalgebras --
----------------

{-| This type represents a coalgebra over a functor @f@ and carrier @a@. -}
type Coalg f a = a -> f a a

{-| Construct an anamorphism from the given coalgebra. -}
ana :: forall a f . Difunctor f => Coalg f a -> a -> Term f
ana f = run
    where run :: a -> Term f
          run t = Term $ fmap run (f t)

-- | Shortcut fusion variant of 'ana'.
ana' :: forall a f . Functor f => Coalg f a -> a -> Term f
ana' f t = build $ run t
    where run :: forall b . a -> Alg f b -> b
          run t con = run' t where
              run' :: a ->  b
              run' t = con $ fmap run' (f t)

build :: (forall a. Alg f a -> a) -> Term f
{-# INLINE [1] build #-}
build g = g Term

{-| This type represents a monadic coalgebra over a functor @f@ and carrier
  @a@. -}
type CoalgM m f a = a -> m (f a)

{-| Construct a monadic anamorphism from the given monadic coalgebra. -}
anaM :: forall a m f. (Traversable f, Monad m)
          => CoalgM m f a -> a -> m (Term f)
anaM f = run 
    where run :: a -> m (Term f)
          run t = liftM Term $ f t >>= mapM run


--------------------------------
-- R-Algebras & Paramorphisms --
--------------------------------

{-| This type represents an r-algebra over a functor @f@ and carrier @a@. -}
type RAlg f a = f (Term f, a) -> a

{-| Construct a paramorphism from the given r-algebra. -}
para :: (Functor f) => RAlg f a -> Term f -> a
para f = snd . cata run
    where run t = (Term $ fmap fst t, f t)

{-| This type represents a monadic r-algebra over a functor @f@ and carrier
  @a@. -}
type RAlgM m f a = f (Term f, a) -> m a

{-| Construct a monadic paramorphism from the given monadic r-algebra. -}
paraM :: (Traversable f, Monad m) => 
         RAlgM m f a -> Term f -> m a
paraM f = liftM snd . cataM run
    where run t = do
            a <- f t
            return (Term $ fmap fst t, a)

--------------------------------
-- R-Coalgebras & Apomorphisms --
--------------------------------

{-| This type represents an r-coalgebra over a functor @f@ and carrier @a@. -}
type RCoalg f a = a -> f (Either (Term f) a)

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


----------------------------------
-- CV-Algebras & Histomorphisms --
----------------------------------

{-| This type represents a cv-algebra over a functor @f@ and carrier @a@. -}
type CVAlg f a f' = f (Term f') -> a


-- | This function applies 'projectP' at the tip of the term.

projectTip  :: (DistProd f a f') => Term f' -> (f (Term f'), a)
projectTip (Term v) = projectP v

{-| Construct a histomorphism from the given cv-algebra. -}
histo :: (Functor f,DistProd f a f') => CVAlg f a f' -> Term f -> a
histo alg  = snd . projectTip . cata run
    where run v = Term $ injectP (alg v) v

{-| This type represents a monadic cv-algebra over a functor @f@ and carrier
  @a@. -}
type CVAlgM m f a f' = f (Term f') -> m a

{-| Construct a monadic histomorphism from the given monadic cv-algebra. -}
histoM :: (Traversable f, Monad m, DistProd f a f') =>
          CVAlgM m f a f' -> Term f -> m a
histoM alg  = liftM (snd . projectTip) . cataM run
    where run v = do r <- alg v
                     return $ Term $ injectP r v

-----------------------------------
-- CV-Coalgebras & Futumorphisms --
-----------------------------------

{-| This type represents a cv-coalgebra over a functor @f@ and carrier @a@. -}
type CVCoalg f a = a -> f (Context f a)

{-| Construct a futumorphism from the given cv-coalgebra. -}
futu :: forall f a . Functor f => CVCoalg f a -> a -> Term f
futu coa = ana run . Hole
    where run :: Coalg f (Context f a)
          run (Hole x) = coa x
          run (Term t) = t

{-| This type represents a monadic cv-coalgebra over a functor @f@ and carrier
  @a@. -}
type CVCoalgM m f a = a -> m (f (Context f a))

{-| Construct a monadic futumorphism from the given monadic cv-coalgebra. -}
futuM :: forall f a m . (Traversable f, Monad m) =>
         CVCoalgM m f a -> a -> m (Term f)
futuM coa = anaM run . Hole
    where run :: CoalgM m f (Context f a)
          run (Hole x) = coa x
          run (Term t) = return t

{-| This type represents a generalised cv-coalgebra over a functor @f@ and
  carrier @a@. -}
type CVCoalg' f a = a -> Context f a

{-| Construct a futumorphism from the given generalised cv-coalgebra. -}
futu' :: forall f a . Functor f => CVCoalg' f a -> a -> Term f
futu' coa = run
    where run :: a -> Term f
          run x = appCxt $ fmap run (coa x)


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

{-# RULES 
  "cataM/appTermHomM" forall (a :: AlgM m g d) (h :: TermHomM m f g) x.
     appTermHomM h x >>= cataM a = cataM (compAlgM a h) x;

  "cataM/appTermHom" forall (a :: AlgM m g d) (h :: TermHom f g) x.
     cataM a (appTermHom h x) = cataM (compAlgM' a h) x;

  "appTermHomM/appTermHomM" forall (a :: TermHomM m g h) (h :: TermHomM m f g) x.
    appTermHomM h x >>= appTermHomM a = appTermHomM (compTermHomM a h) x;
 #-}

{-# RULES
  "cata/build"  forall alg (g :: forall a . Alg f a -> a) .
                cata alg (build g) = g alg
 #-}
#endif
-}