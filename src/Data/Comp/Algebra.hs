{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeOperators,
  FlexibleContexts, CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Algebra
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the notion of algebras and catamorphisms, and their
-- generalizations to e.g. monadic versions and other (co)recursion schemes.
--
--------------------------------------------------------------------------------

module Data.Comp.Algebra (
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
      appTermHom',
      compTermHom,
      appSigFun,
      appSigFun',
      compSigFun,
      compSigFunTermHom,
      compTermHomSigFun,
      compAlgSigFun,
      termHom,
      compAlg,
      compCoalg,
      compCVCoalg,

      -- * Monadic Term Homomorphisms
      CxtFunM,
      SigFunM,
      TermHomM,
      SigFunMD,
      TermHomMD,
      sigFunM,
      termHom',
      appTermHomM,
      appTermHomM',
      termHomM,
      termHomMD,
      appSigFunM,
      appSigFunM',
      appSigFunMD,
      appAlgTermHomM,
      appAlgSigFunM,
      compTermHomM,
      compSigFunM,
      compSigFunTermHomM,
      compTermHomSigFunM,
      compAlgSigFunM,
      compAlgM,
      compAlgM',

      -- * Coalgebras & Anamorphisms
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
      futuM
    ) where

import Data.Comp.Term
import Data.Comp.Ops
import Data.Traversable
import Control.Monad hiding (sequence, mapM)

import Prelude hiding (sequence, mapM)



{-| This type represents an algebra over a functor @f@ and carrier
@a@. -}

type Alg f a = f a -> a

{-| Construct a catamorphism for contexts over @f@ with holes of type @a@, from
  the given algebra. -}
free :: forall f h a b . (Functor f) => Alg f b -> (a -> b) -> Cxt h f a -> b
free f g = run
    where run :: Cxt h f a -> b
          run (Hole x) = g x
          run (Term t) = f (fmap run t)

{-| Construct a catamorphism from the given algebra. -}
cata :: forall f a . (Functor f) => Alg f a -> Term f -> a 
{-# NOINLINE [1] cata #-}
-- cata f = free f undefined
-- the above definition is safe since terms do not contain holes
--
-- a direct implementation:
cata f = run 
    where run :: Term f -> a
          run  = f . fmap run . unTerm


{-| A generalisation of 'cata' from terms over @f@ to contexts over @f@, where
  the holes have the type of the algebra carrier. -}
cata' :: (Functor f) => Alg f a -> Cxt h f a -> a
{-# INLINE cata' #-}
cata' f = free f id


{-| This function applies a whole context into another context. -}

appCxt :: (Functor f) => Context f (Cxt h f a) -> Cxt h f a
-- appCxt = cata' Term
appCxt (Hole x) = x
appCxt (Term t) = Term (fmap appCxt t)



{-| This type represents a monadic algebra. It is similar to 'Alg' but
the return type is monadic.  -}

type AlgM m f a = f a -> m a 

{-| Convert a monadic algebra into an ordinary algebra with a monadic
  carrier. -}
algM :: (Traversable f, Monad m) => AlgM m f a -> Alg f (m a)
algM f x = sequence x >>= f

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @a@, from the given monadic algebra. -}
freeM :: forall h f a m b. (Traversable f, Monad m) =>
               AlgM m f b -> (a -> m b) -> Cxt h f a -> m b
-- freeM alg var = free (algM alg) var
freeM algm var = run
    where run :: Cxt h f a -> m b
          run (Hole x) = var x
          run (Term t) = algm =<< mapM run t

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM :: forall f m a. (Traversable f, Monad m) => AlgM m f a -> Term f -> m a 
{-# NOINLINE [1] cataM #-}
-- cataM = cata . algM
cataM algm = run
    where run :: Term f -> m a
          run = algm <=< mapM run . unTerm

{-| A generalisation of 'cataM' from terms over @f@ to contexts over @f@, where
  the holes have the type of the monadic algebra carrier. -}
cataM' :: forall h f a m . (Traversable f, Monad m)
            => AlgM m f a -> Cxt h f a -> m a
{-# NOINLINE [1] cataM' #-}
-- cataM' f = free (\x -> sequence x >>= f) return
cataM' f = run
    where run :: Cxt h f a -> m a
          run (Hole x) = return x
          run (Term t) = f =<< mapM run t


{-| This type represents a context function. -}
type CxtFun f g = forall a h. Cxt h f a -> Cxt h g a

{-| This type represents a signature function.-}
type SigFun f g = forall a. f a -> g a

{-| This type represents a term homomorphism. -}
type TermHom f g = SigFun f (Context g)

{-| Apply a term homomorphism recursively to a term/context. -}
appTermHom :: (Traversable f, Functor g) => TermHom f g -> CxtFun f g
{-# INLINE [1] appTermHom #-}
-- Constraint Traversable f is not essential and can be replaced by
-- Functor f. It is, however, needed for the shortcut-fusion rules to
-- work.
appTermHom = appTermHom_

{-| This function applies the given term homomorphism to a
term/context. -}
appTermHom_ :: forall f g . (Functor f, Functor g) => TermHom f g -> CxtFun f g
{-# NOINLINE [1] appTermHom_ #-}
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (Cxt h g b) -> Context g (Cxt h g b)) -> Cxt h f b -> Cxt h g b
-- would achieve the same. The given type is chosen for clarity.
appTermHom_ f = run where
    run :: CxtFun f g
    run (Hole x) = Hole x
    run (Term t) = appCxt (f (fmap run t))

-- | Apply a term homomorphism recursively to a term/context. This is
-- a top-down variant of 'appTermHom'.
appTermHom' :: forall f g . (Functor g) => TermHom f g -> CxtFun f g
{-# NOINLINE [1] appTermHom' #-}
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (Cxt h g b) -> Context g (Cxt h g b)) -> Cxt h f b -> Cxt h g b
-- would achieve the same. The given type is chosen for clarity.
appTermHom' f = run where
    run :: CxtFun f g
    run (Hole x) = Hole x
    run (Term t) = appCxt  (fmap run (f t))

{-| Compose two term homomorphisms. -}
compTermHom :: (Functor g, Functor h) => TermHom g h -> TermHom f g -> TermHom f h
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (Cxt h g b) -> Context g (Cxt h g b))
-- -> (a -> Cxt h f b) -> a -> Cxt h g b
-- would achieve the same. The given type is chosen for clarity.
compTermHom f g = appTermHom_ f . g

{-| Compose an algebra with a term homomorphism to get a new algebra. -}
compAlg :: (Functor g) => Alg g a -> TermHom f g -> Alg f a
compAlg alg talg = cata' alg . talg

{-| Compose a term homomorphism with a coalgebra to get a cv-coalgebra. -}
compCoalg :: TermHom f g -> Coalg f a -> CVCoalg' g a
compCoalg hom coa = hom . coa

{-| Compose a term homomorphism with a cv-coalgebra to get a new cv-coalgebra.
 -}
compCVCoalg :: (Functor f, Functor g)
  => TermHom f g -> CVCoalg' f a -> CVCoalg' g a
compCVCoalg hom coa = appTermHom_ hom . coa


{-| This function applies a signature function to the given context. -}
appSigFun :: (Functor f) => SigFun f g -> CxtFun f g
{-# NOINLINE [1] appSigFun #-}
appSigFun f = run
    where run (Term t) = Term $ f $ fmap run t
          run (Hole x) = Hole x
-- implementation via term homomorphisms:
--  appSigFun f = appTermHom_ $ termHom f

-- | This function applies a signature function to the given
-- context. This is a top-down variant of 'appSigFun'.
appSigFun' :: (Functor g) => SigFun f g -> CxtFun f g
{-# NOINLINE [1] appSigFun' #-}
appSigFun' f = run
    where run (Term t) = Term $ fmap run  $ f t
          run (Hole x) = Hole x


{-| This function composes two signature functions. -}
compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g

-- | This function composes a signature function with a term
-- homomorphism.
compSigFunTermHom :: (Functor g) => SigFun g h -> TermHom f g -> TermHom f h
compSigFunTermHom f g = appSigFun f . g

-- | This function composes a term homomorphism with a signature function.
compTermHomSigFun :: TermHom g h -> SigFun f g -> TermHom f h
compTermHomSigFun f g = f . g

-- | This function composes an algebra with a signature function.
compAlgSigFun :: Alg g a -> SigFun f g -> Alg f a
compAlgSigFun f g = f . g


-- | Lifts the given signature function to the canonical term
-- homomorphism.
termHom :: (Functor g) => SigFun f g -> TermHom f g
termHom f = simpCxt . f

{-|
  This type represents a monadic context function.
-}
type CxtFunM m f g = forall a h. Cxt h f a -> m (Cxt h g a)

{-| This type represents a monadic signature function. -}

type SigFunM m f g = forall a. f a -> m (g a)

{-| This type represents a monadic signature function.  It is similar
to 'SigFunM' but has monadic values also in the domain. -}
type SigFunMD m f g = forall a. f (m a) -> m (g a)

{-| This type represents a monadic term homomorphism.  -}
type TermHomM m f g = SigFunM m f (Context g)

{-| This type represents a monadic term homomorphism. It is similar to
'TermHomM' but has monadic values also in the domain. -}
type TermHomMD m f g = SigFunMD m f (Context g)


{-| Lift the given signature function to a monadic signature function. Note that
  term homomorphisms are instances of signature functions. Hence this function
  also applies to term homomorphisms. -}
sigFunM :: (Monad m) => SigFun f g -> SigFunM m f g
sigFunM f = return . f

{-| Lift the give monadic signature function to a monadic term homomorphism. -}
termHom' :: (Functor f, Functor g, Monad m) => SigFunM m f g -> TermHomM m f g
termHom' f = liftM  (Term . fmap Hole) . f

{-| Lift the given signature function to a monadic term homomorphism. -}
termHomM :: (Functor g, Monad m) => SigFun f g -> TermHomM m f g
termHomM f = sigFunM $ termHom f


{-| Apply a monadic term homomorphism recursively to a term/context. -}
appTermHomM :: forall f g m . (Traversable f, Functor g, Monad m)
         => TermHomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appTermHomM #-}
appTermHomM f = run
    where run :: Cxt h f a -> m (Cxt h g a)
          run (Hole x) = return (Hole x)
          run (Term t) = liftM appCxt . f =<< mapM run t

-- | Apply a monadic term homomorphism recursively to a
-- term/context. This a top-down variant of 'appTermHomM'.
appTermHomM' :: forall f g m . (Traversable g, Monad m)
         => TermHomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appTermHomM' #-}
appTermHomM' f = run
    where run :: Cxt h f a -> m (Cxt h g a)
          run (Hole x) = return (Hole x)
          run (Term t) = liftM appCxt . mapM run =<< f t

{-| This function constructs the unique monadic homomorphism from the
initial term algebra to the given term algebra. -}
termHomMD :: forall f g m . (Traversable f, Functor g, Monad m)
          => TermHomMD m f g -> CxtFunM m f g
termHomMD f = run 
    where run :: Cxt h f a -> m (Cxt h g a)
          run (Hole x) = return (Hole x)
          run (Term t) = liftM appCxt (f (fmap run t))


{-| This function applies a monadic signature function to the given context. -}
appSigFunM :: (Traversable f, Monad m) => SigFunM m f g -> CxtFunM m f g
{-# NOINLINE [1] appSigFunM #-}
appSigFunM f = run
    where run (Term t) = liftM Term . f =<< mapM run t
          run (Hole x) = return (Hole x)
-- implementation via term homomorphisms
-- appSigFunM f = appTermHomM $ termHom' f



-- | This function applies a monadic signature function to the given
-- context. This is a top-down variant of 'appSigFunM'.
appSigFunM' :: (Traversable g, Monad m) => SigFunM m f g -> CxtFunM m f g
{-# NOINLINE [1] appSigFunM' #-}
appSigFunM' f = run
    where run (Term t) = liftM Term . mapM run =<< f t
          run (Hole x) = return (Hole x)

{-| This function applies a signature function to the given context. -}
appSigFunMD :: forall f g m . (Traversable f, Functor g, Monad m)
              => SigFunMD m f g -> CxtFunM m f g
appSigFunMD f = run 
    where run :: Cxt h f a -> m (Cxt h g a)
          run (Hole x) = return (Hole x)
          run (Term t) = liftM Term (f (fmap run t))

{-| Compose two monadic term homomorphisms. -}
compTermHomM :: (Traversable g, Functor h, Monad m)
             => TermHomM m g h -> TermHomM m f g -> TermHomM m f h
compTermHomM f g = appTermHomM f <=< g

{-| Compose a monadic algebra with a monadic term homomorphism to get a new
  monadic algebra. -}
compAlgM :: (Traversable g, Monad m) => AlgM m g a -> TermHomM m f g -> AlgM m f a
compAlgM alg talg = cataM' alg <=< talg


-- | This function applies the given algebra bottom-up while applying
-- the given term homomorphism top-down. Thereby we have no
-- requirements on the source signature @f@.
appAlgTermHomM :: forall m f g a. (Traversable g, Monad m)
               => AlgM m g a -> TermHomM m f g -> Term f -> m a
appAlgTermHomM alg hom = run
    where run :: Term f -> m a
          run (Term t) = hom t >>= mapM run >>= run'
          run' :: (Context g a) -> m a
          run' (Term t) = mapM run' t >>= alg
          run' (Hole x) = return x

-- | This function applies the given algebra bottom-up while applying
-- the given signature function top-down. Thereby we have no
-- requirements on the source signature @f@.
appAlgSigFunM :: forall m f g a. (Traversable g, Monad m)
               => AlgM m g a -> SigFunM m f g -> Term f -> m a
appAlgSigFunM alg sig = run
    where run :: Term f -> m a
          run (Term t) = sig t >>= mapM run >>= alg

{-| Compose a monadic algebra with a term homomorphism to get a new monadic
  algebra. -}
compAlgM' :: (Traversable g, Monad m) => AlgM m g a -> TermHom f g -> AlgM m f a
compAlgM' alg talg = cataM' alg . talg


{-| This function composes two monadic signature functions.  -}
compSigFunM :: (Monad m) => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g = f <=< g

compSigFunTermHomM :: (Traversable g, Functor h, Monad m)
                   => SigFunM m g h -> TermHomM m f g -> TermHomM m f h
compSigFunTermHomM f g = appSigFunM f <=< g

{-| This function composes two monadic signature functions.  -}
compTermHomSigFunM :: (Monad m) => TermHomM m g h -> SigFunM m f g -> TermHomM m f h
compTermHomSigFunM f g = f <=< g


{-| This function composes two monadic signature functions.  -}
compAlgSigFunM :: (Monad m) => AlgM m g a -> SigFunM m f g -> AlgM m f a
compAlgSigFunM f g = f <=< g

----------------
-- Coalgebras --
----------------

{-| This type represents a coalgebra over a functor @f@ and carrier @a@. -}
type Coalg f a = a -> f a

{-| Construct an anamorphism from the given coalgebra. -}
ana :: forall a f . Functor f => Coalg f a -> a -> Term f
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


-- | This function applies 'projectA' at the tip of the term.
projectTip  :: (DistAnn f a f') => Term f' -> (f (Term f'), a)
projectTip (Term v) = projectA v

{-| Construct a histomorphism from the given cv-algebra. -}
histo :: (Functor f,DistAnn f a f') => CVAlg f a f' -> Term f -> a
histo alg  = snd . projectTip . cata run
    where run v = Term $ injectA (alg v) v

{-| This type represents a monadic cv-algebra over a functor @f@ and carrier
  @a@. -}
type CVAlgM m f a f' = f (Term f') -> m a

{-| Construct a monadic histomorphism from the given monadic cv-algebra. -}
histoM :: (Traversable f, Monad m, DistAnn f a f') =>
          CVAlgM m f a f' -> Term f -> m a
histoM alg  = liftM (snd . projectTip) . cataM run
    where run v = do r <- alg v
                     return $ Term $ injectA r v

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

--  "appSigFun/appTermHom" forall (f :: SigFun g h) (g :: TermHom f g) x.
--    appSigFun f (appTermHom g x) = appTermHom (compSigFunTermHom f g) x;

  "appTermHom/appSigFun" forall (f :: TermHom g h) (g :: SigFun f g) x.
    appTermHom f (appSigFun g x) = appTermHom_ (compTermHomSigFun f g) x;

  "cata/appSigFun" forall (f :: Alg g a) (g :: SigFun f g) x.
    cata f (appSigFun g x) = cata (compAlgSigFun f g) x;
 #-}

{-# RULES 
  "cataM/appTermHomM" forall (a :: AlgM m g d) (h :: TermHomM m f g) x.
     appTermHomM h x >>= cataM a = cataM (compAlgM a h) x;

  "cataM/appTermHomM'" forall (a :: AlgM m g d) (h :: TermHomM m f g) x.
     appTermHomM' h x >>= cataM a = appAlgTermHomM a h x;

  "cataM/appSigFunM'" forall (a :: AlgM m g d) (h :: SigFunM m f g) x.
     appSigFunM' h x >>= cataM a = appAlgSigFunM a h x;

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
