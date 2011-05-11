{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeOperators,
  FlexibleContexts, CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Algebra
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
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable

import Unsafe.Coerce (unsafeCoerce)

{-| This type represents an algebra over a difunctor @f@ and carrier @a@. -}
type Alg f a = f a a -> a

{-| Construct a catamorphism for contexts over @f@ with holes of type @b@, from
  the given algebra. -}
free :: forall h f a b. Difunctor f
        => Alg f a -> (b -> a) -> Cxt h f a b -> a
free f g = run
    where run :: Cxt h f a b -> a
          run (Term t) = f (fmap run t)
          run (Hole x) = g x
          run (Place p) = p

{-| Construct a catamorphism from the given algebra. -}
cata :: forall f a. Difunctor f => Alg f a -> Term f -> a 
{-# NOINLINE [1] cata #-}
cata f = run . coerceCxt
    where run :: Cxt NoHole f a () -> a
          run (Term t) = f (fmap run t)
          run (Place x) = x

{-| A generalisation of 'cata' from terms over @f@ to contexts over @f@, where
  the holes have the type of the algebra carrier. -}
cata' :: Difunctor f => Alg f a -> Cxt h f a a -> a
{-# INLINE cata' #-}
cata' f = free f id

{-| This function applies a whole context into another context. -}
appCxt :: Difunctor f => Context f a (Cxt h f a b) -> Cxt h f a b
appCxt (Term t) = Term (fmap appCxt t)
appCxt (Hole x) = x
appCxt (Place p) = Place p

{-| This type represents a monadic algebra. It is similar to 'Alg' but
  the return type is monadic. -}
type AlgM m f a = f a a -> m a

{-| Convert a monadic algebra into an ordinary algebra with a monadic
  carrier. -}
algM :: (Ditraversable f m a, Monad m) => AlgM m f a -> Alg f (m a)
algM f x = disequence (dimap return id x) >>= f

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @b@, from the given monadic algebra. -}
freeM :: forall m h f a b. (Ditraversable f m a, Monad m)
         => AlgM m f a -> (b -> m a) -> Cxt h f a b -> m a
freeM f g = run
    where run :: Cxt h f a b -> m a
          run (Term t) = f =<< dimapM run t
          run (Hole x) = g x
          run (Place p) = return p

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM :: forall m f a. (Ditraversable f m a, Monad m)
         => AlgM m f a -> Term f -> m a
{-# NOINLINE [1] cataM #-}
cataM algm = run . coerceCxt
    where run :: Cxt NoHole f a () -> m a
          run (Term t) = algm =<< dimapM run t
          run (Place x) = return x

{-| A generalisation of 'cataM' from terms over @f@ to contexts over @f@, where
  the holes have the type of the monadic algebra carrier. -}
cataM' :: forall m h f a. (Ditraversable f m a, Monad m)
          => AlgM m f a -> Cxt h f a (m a) -> m a
{-# NOINLINE [1] cataM' #-}
cataM' f = freeM f id

{-| This type represents a context function. -}
type CxtFun f g = forall h a b. Cxt h f a b -> Cxt h g a b


{-| This type represents a signature function. -}
type SigFun f g = forall a b. f a b -> g a b

{-| This type represents a term homomorphism. -}
type TermHom f g = SigFun f (Context g)

{-| Apply a term homomorphism recursively to a term/context. -}
appTermHom :: forall f g. (Difunctor f, Difunctor g)
              => TermHom f g -> CxtFun f g
{-# INLINE [1] appTermHom #-}
appTermHom f = run where
    run :: CxtFun f g
    run (Term t) = appCxt (f (fmap run t))
    run (Hole x) = Hole x
    run (Place p) = Place p

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
type CxtFunM m f g = forall h a b. Cxt h f a b -> m (Cxt h g a b)

{-| This type represents a monadic context function. -}
type CxtFunM' m f g = forall h b. Cxt h f Any b -> m (Cxt h g Any b)

coerceCxtFunM :: CxtFunM' m f g -> CxtFunM m f g
coerceCxtFunM = unsafeCoerce

{-| This type represents a monadic signature function. -}
type SigFunM m f g = forall a b. f a b -> m (g a b)

{-| This type represents a monadic signature function. It is similar to
  'SigFunM' but has monadic values also in the domain. -}
type SigFunM' m f g = forall a b. f a (m b) -> m (g a b)

{-| This type represents a monadic term homomorphism. -}
type TermHomM m f g = SigFunM m f (Context g)

{-| This type represents a monadic term homomorphism. It is similar to
  'TermHomM' but has monadic values also in the domain. -}
type TermHomM' m f g = SigFunM' m f (Context g)

{-| Lift the given signature function to a monadic signature function. Note that
  term homomorphisms are instances of signature functions. Hence this function
  also applies to term homomorphisms. -}
sigFunM :: Monad m => SigFun f g -> SigFunM m f g
sigFunM f = return . f

{-| Lift the give monadic signature function to a monadic term homomorphism. -}
termHom' :: (Difunctor f, Difunctor g, Monad m)
            => SigFunM m f g -> TermHomM m f g
termHom' f = liftM  (Term . fmap Hole) . f

{-| Lift the given signature function to a monadic term homomorphism. -}
termHomM :: (Difunctor g, Monad m) => SigFun f g -> TermHomM m f g
termHomM f = sigFunM $ termHom f

-- | Apply a monadic term homomorphism recursively to a
-- term/context. The monad is sequenced bottom-up.
appTermHomM :: forall f g m. (Ditraversable f m Any, Difunctor g)
               => TermHomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appTermHomM #-}
appTermHomM f = coerceCxtFunM run
    where run :: CxtFunM' m f g
          run (Term t) = liftM appCxt (f =<< dimapM run t)
          run (Hole x) = return (Hole x)
          run (Place p) = return (Place p)


-- | Apply a monadic term homomorphism recursively to a
-- term/context. The monad is sequence top-down.
appTermHomM' :: forall f g m. (Ditraversable g m Any)
         => TermHomM m f g ->  CxtFunM m f g
appTermHomM' f = coerceCxtFunM run
    where run :: CxtFunM' m f g
          run (Term t)  = liftM appCxt . disequenceCxt . fmapCxt run =<< f t
          run (Place p) = return (Place p)
          run (Hole x) = return (Hole x)
            

{-| This function constructs the unique monadic homomorphism from the
  initial term algebra to the given term algebra. -}
termHomM' :: forall f g m. (Difunctor f, Difunctor g, Monad m)
             => TermHomM' m f g -> CxtFunM m f g
termHomM' f = run 
    where run :: CxtFunM m f g
          run (Term t) = liftM appCxt (f (fmap run t))
          run (Hole x) = return (Hole x)
          run (Place p) = return (Place p)

{-| This function applies a monadic signature function to the given context. -}
appSigFunM :: (Ditraversable f m Any, Difunctor g, Monad m)
              => SigFunM m f g -> CxtFunM m f g
appSigFunM f = appTermHomM $ termHom' f

{-| This function applies a signature function to the given context. -}
appSigFunM' :: forall f g m. (Ditraversable f m Any, Difunctor g, Monad m)
               => SigFunM' m f g -> CxtFunM m f g
appSigFunM' f = run 
    where run :: CxtFunM m f g
          run (Term t) = liftM Term (f (fmap run t))
          run (Hole x) = return (Hole x)
          run (Place p) = return (Place p)

{-| Compose two monadic term homomorphisms. -}
compTermHomM :: (Ditraversable g m Any, Difunctor h, Monad m)
                => TermHomM m g h -> TermHomM m f g -> TermHomM m f h
compTermHomM f g = appTermHomM f <=< g

{-| Compose a monadic algebra with a monadic term homomorphism to get a new
  monadic algebra. -}
compAlgM :: (Ditraversable g m a, Monad m)
            => AlgM m g a -> TermHomM m f g -> AlgM m f a
compAlgM alg talg = freeM alg return <=< talg

{-| Compose a monadic algebra with a term homomorphism to get a new monadic
  algebra. -}
compAlgM' :: (Ditraversable g m a, Monad m) => AlgM m g a
          -> TermHom f g -> AlgM m f a
compAlgM' alg talg = freeM alg return . talg

{-| This function composes two monadic signature functions. -}
compSigFunM :: Monad m => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g a = g a >>= f


----------------
-- Coalgebras --
----------------

{-| This type represents a coalgebra over a difunctor @f@ and carrier @a@. The
  list of @(a,b)@s represent the parameters that may occur in the constructed
  value. The first component represents the seed of the parameter,
  and the second component is the (polymorphic) parameter itself. If @f@ is
  itself a binder, then the parameters bound by @f@ can be passed to the
  covariant argument, thereby making them available to sub terms. -}
type Coalg f a = forall b. a -> [(a,b)] -> Either b (f b (a,[(a,b)]))

{-| Construct an anamorphism from the given coalgebra. -}
ana :: forall a f. Difunctor f => Coalg f a -> a -> Term f
ana f x = run (x,[])
    where run (a,bs) = case f a bs of
                         Left p -> Place p
                         Right t -> Term $ fmap run t

{-| This type represents a monadic coalgebra over a difunctor @f@ and carrier
  @a@. -}
type CoalgM m f a = forall b. a -> [(a,b)] -> m (Either b (f b (a,[(a,b)])))

{-| Construct a monadic anamorphism from the given monadic coalgebra. -}
anaM :: forall a m f. (Ditraversable f m Any, Monad m)
     => CoalgM m f a -> a -> m (Term f)
anaM f x = run (x,[])
    where run (a,bs) = do c <- f a bs
                          case c of
                            Left p -> return $ Place p
                            Right t -> liftM Term $ dimapM run t


--------------------------------
-- R-Algebras & Paramorphisms --
--------------------------------

{-| This type represents an r-algebra over a difunctor @f@ and carrier @a@. -}
type RAlg f a = f a (Cxt NoHole f a (), a) -> a

{-| Construct a paramorphism from the given r-algebra. -}
para :: forall f a. Difunctor f => RAlg f a -> Term f -> a
para f = run . coerceCxt
    where run :: Cxt NoHole f a () -> a
          run (Term t) = f $ fmap (\x -> (x, run x)) t
          run (Place x) = x

{-| This type represents a monadic r-algebra over a difunctor @f@ and carrier
  @a@. -}
type RAlgM m f a = f a (Cxt NoHole f a (), a) -> m a
{-| Construct a monadic paramorphism from the given monadic r-algebra. -}
paraM :: forall m f a. (Ditraversable f m a, Monad m)
         => RAlgM m f a -> Term f -> m a
paraM f = run . coerceCxt
    where run :: Cxt NoHole f a () -> m a
          run (Term t) = f =<< dimapM (\x -> run x >>= \y -> return (x, y)) t
          run (Place x) = return x


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
type CVAlg f a f' = f a (Cxt NoHole f' a ()) -> a

-- | This function applies 'projectA' at the tip of the term.
projectTip  :: DistAnn f a f' => Cxt NoHole f' a () -> a
projectTip (Term v) = snd $ projectA v
projectTip (Place p) = p

{-| Construct a histomorphism from the given cv-algebra. -}
histo :: forall f f' a. (Difunctor f, DistAnn f a f')
         => CVAlg f a f' -> Term f -> a
histo alg = projectTip . cata run
    where run :: Alg f (Cxt NoHole f' a ())
          run v = Term $ injectA (alg v') v'
              where v' = dimap Place id v

{-| This type represents a monadic cv-algebra over a functor @f@ and carrier
  @a@. -}
type CVAlgM m f a f' = f a (Cxt NoHole f' a ()) -> m a

{-| Construct a monadic histomorphism from the given monadic cv-algebra. -}
histoM :: forall f f' m a. (Ditraversable f m a, Monad m, DistAnn f a f')
          => CVAlgM m f a f' -> Term f -> m a
histoM alg = liftM projectTip . run . coerceCxt
    where run (Term t) = do t' <- dimapM run t
                            r <- alg t'
                            return $ Term $ injectA r t'
          run (Place p) = return $ Place p


-----------------------------------
-- CV-Coalgebras & Futumorphisms --
-----------------------------------

{-| This type represents a cv-coalgebra over a difunctor @f@ and carrier @a@.
  The list of @(a,b)@s represent the parameters that may occur in the
  constructed value. The first component represents the seed of the parameter,
  and the second component is the (polymorphic) parameter itself. If @f@ is
  itself a binder, then the parameters bound by @f@ can be passed to the
  covariant argument, thereby making them available to sub terms. -}
type CVCoalg f a = forall b. a -> [(a,b)]
                 -> Either b (f b (Context f b (a,[(a,b)])))

{-| Construct a futumorphism from the given cv-coalgebra. -}
futu :: forall f a. Difunctor f => CVCoalg f a -> a -> Term f
futu coa x = run (x,[])
    where run (a,bs) = case coa a bs of
                         Left p -> Place p
                         Right t -> Term $ fmap run' t
          run' (Term t) = Term $ fmap run' t
          run' (Hole x) = run x
          run' (Place p) = Place p

{-| This type represents a monadic cv-coalgebra over a difunctor @f@ and carrier
  @a@. -}
type CVCoalgM m f a = forall b. a -> [(a,b)]
                    -> m (Either b (f b (Context f b (a,[(a,b)]))))

{-| Construct a monadic futumorphism from the given monadic cv-coalgebra. -}
futuM :: forall f a m. (Ditraversable f m Any, Monad m) =>
         CVCoalgM m f a -> a -> m (Term f)
futuM coa x = run (x,[])
    where run (a,bs) = do c <- coa a bs
                          case c of 
                            Left p -> return $ Place p
                            Right t -> liftM Term $ dimapM run' t
          run' (Term t) = liftM Term $ dimapM run' t
          run' (Hole x) = run x
          run' (Place p) = return $ Place p

{-| This type represents a generalised cv-coalgebra over a difunctor @f@ and
  carrier @a@. -}
type CVCoalg' f a = forall b. a -> [(a,b)] -> Context f b (a,[(a,b)])

{-| Construct a futumorphism from the given generalised cv-coalgebra. -}
futu' :: forall f a. Difunctor f => CVCoalg' f a -> a -> Term f
futu' coa x = run (x,[])
    where run (a,bs) = run' $ coa a bs
          run' (Term t) = Term $ fmap run' t
          run' (Hole x) = run x
          run' (Place p) = Place p

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