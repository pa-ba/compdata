{-# LANGUAGE GADTs, RankNTypes, TypeOperators, ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Multi.Algebra
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines the central notion of /terms/ and its
-- generalisation to contexts.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Multi.Algebra where
    
import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.HFunctor

import Control.Monad

type Alg f e = f e :-> e

-- | The identity Functor.
data I a = I {unI :: a}

-- | The parametrised constant functor.
data K a b = K {unK :: a}


freeAlgHom :: forall f h a b . (HFunctor f) =>
              Alg f b -> (a :-> b) -> Cxt h f a :-> b
freeAlgHom f g = run
    where run :: Cxt h f a :-> b
          run (Hole v) = g v
          run (Term c) = f $ hfmap run c


cata :: forall f a. (HFunctor f) => Alg f a -> Term f :-> a
cata f = run 
    where run :: Term f :-> a
          run (Term t) = f (hfmap run t)

cata' :: (HFunctor f) => Alg f e -> Cxt h f e :-> e
cata' alg = freeAlgHom alg id

-- | This function applies a whole context into another context.

applyCxt :: (HFunctor f) => Context f (Cxt h f a) :-> Cxt h f a
applyCxt = cata' Term

type AlgM m f e = NatM m (f e) e

freeAlgHomM :: forall f m h a b. (HTraversable f, Monad m) =>
               AlgM m f b -> (NatM m a b) -> NatM m (Cxt h f a)  b
freeAlgHomM algm var = run
    where run :: NatM m (Cxt h f a) b
          run (Hole x) = var x
          run (Term x) = hmapM run x >>= algm

-- | This is a monadic version of 'cata'.

cataM :: forall f m a. (HTraversable f, Monad m) =>
         AlgM m f a -> NatM m (Term f) a
-- cataM alg h (Term t) = alg =<< hmapM (cataM alg h) t
cataM alg = run
    where run :: NatM m (Term f) a
          run (Term x) = alg =<< hmapM run x


cataM' :: forall m h a f. (Monad m, HTraversable f) => AlgM m f a -> NatM m (Cxt h f a) a
-- cataM' alg = freeAlgHomM alg return
cataM' f = run
    where run :: NatM m (Cxt h f a) a
          run (Hole x) = return x
          run (Term x) = hmapM run x >>= f

-- | This type represents context function.

type CxtFun f g = forall a h. Cxt h f a :-> Cxt h g a

-- | This type represents uniform signature function specification.

type SigFun f g = forall a. f a :-> g a


-- | This type represents a term algebra.

type TermHom f g = SigFun f (Context g)

-- | This function applies the given term homomorphism to a
-- term/context.

applyTermHom :: (HFunctor f, HFunctor g) => TermHom f g -> CxtFun f g
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (Cxt h g b) -> Context g (Cxt h g b)) -> Cxt h f b -> Cxt h g b
-- would achieve the same. The given type is chosen for clarity.
applyTermHom _ (Hole b) = Hole b
applyTermHom f (Term t) = applyCxt . f . hfmap (applyTermHom f) $ t

-- | This function composes two term algebras.

compTermHom :: (HFunctor g, HFunctor h) => TermHom g h -> TermHom f g -> TermHom f h
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (Cxt h g b) -> Context g (Cxt h g b))
-- -> (a -> Cxt h f b) -> a -> Cxt h g b
-- would achieve the same. The given type is chosen for clarity.
compTermHom f g = applyTermHom f . g

-- | This function composes a term algebra with an algebra.

compAlg :: (HFunctor g) => Alg g a -> TermHom f g -> Alg f a
compAlg alg talg = cata' alg . talg

-- | This function applies a signature function to the given context.

applySigFun :: (HFunctor f, HFunctor g) => SigFun f g -> CxtFun f g
applySigFun f = applyTermHom $ termHom $ f


-- | This function composes two signature functions.

compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g




-- | Lifts the given signature function to the canonical term homomorphism.


termHom :: (HFunctor g) => SigFun f g -> TermHom f g
termHom f = simpCxt . f

-- | This type represents monadic context function.

type CxtFunM m f g = forall a h. NatM m (Cxt h f a) (Cxt h g a)

-- | This type represents monadic signature functions.

type SigFunM m f g = forall a. NatM m (f a) (g a)


-- | This type represents monadic term algebras.

type TermHomM m f g = SigFunM m f (Context g)

-- | This function lifts the given signature function to a monadic
-- signature function. Note that term algebras are instances of
-- signature functions. Hence this function also applies to term
-- algebras.

sigFunM :: (Monad m) => SigFun f g -> SigFunM m f g
sigFunM f = return . f

-- | This function lifts the give monadic signature function to a
-- monadic term algebra.

termHom' :: (HFunctor f, HFunctor g, Monad m) =>
            SigFunM m f g -> TermHomM m f g
termHom' f = liftM  (Term . hfmap Hole) . f

-- | This function lifts the given signature function to a monadic
-- term algebra.

termHomM :: (HFunctor g, Monad m) => SigFun f g -> TermHomM m f g
termHomM f = sigFunM $ termHom f

-- | This function applies the given monadic term homomorphism to the
-- given term/context.

applyTermHomM :: forall f g m . (HTraversable f, HFunctor g, Monad m)
         => TermHomM m f g -> CxtFunM m f g
applyTermHomM f = run
    where run :: NatM m (Cxt h f a) (Cxt h g a)
          run (Hole b) = return $ Hole b
          run (Term t) = liftM applyCxt . (>>= f) . hmapM run $ t

-- | This function applies the given monadic signature function to the
-- given context.

applySigFunM :: (HTraversable f, HFunctor g, Monad m) =>
                SigFunM m f g -> CxtFunM m f g
applySigFunM f = applyTermHomM $ termHom' $ f

-- | This function composes two monadic term algebras.

compTermHomM :: (HTraversable g, HFunctor h, Monad m)
             => TermHomM m g h -> TermHomM m f g -> TermHomM m f h
compTermHomM f g a = g a >>= applyTermHomM f

{-| This function composes a monadic term algebra with a monadic algebra -}

compAlgM :: (HTraversable g, Monad m) => AlgM m g a -> TermHomM m f g -> AlgM m f a
compAlgM alg talg c = cataM' alg =<< talg c

-- | This function composes a monadic term algebra with a monadic
-- algebra.

compAlgM' :: (HTraversable g, Monad m) => AlgM m g a -> TermHom f g -> AlgM m f a
compAlgM' alg talg = cataM' alg . talg


{-| This function composes two monadic signature functions.  -}

compSigFunM :: (Monad m) => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g a = g a >>= f


----------------
-- Coalgebras --
----------------

type Coalg f a = a :-> f a

{-| This function unfolds the given value to a term using the given
unravelling function. This is the unique homomorphism @a -> Term f@
from the given coalgebra of type @a -> f a@ to the final coalgebra
@Term f@. -}

ana :: forall f a. HFunctor f => Coalg f a -> a :-> Term f
ana f = run
    where run :: a :-> Term f
          run t = Term $ hfmap run (f t)

type CoalgM m f a = NatM m a (f a)

-- | This function unfolds the given value to a term using the given
-- monadic unravelling function. This is the unique homomorphism @a ->
-- Term f@ from the given coalgebra of type @a -> f a@ to the final
-- coalgebra @Term f@.

anaM :: forall a m f. (HTraversable f, Monad m)
          => CoalgM m f a -> NatM m a (Term f)
anaM f = run 
    where run :: NatM m a (Term f)
          run t = liftM Term $ f t >>= hmapM run

--------------------------------
-- R-Algebras & Paramorphisms --
--------------------------------

-- | This type represents r-algebras over functor @f@ and with domain
-- @a@.

type RAlg f a = f (Term f :&: a) :-> a

-- | This function constructs a paramorphism from the given r-algebra
para :: (HFunctor f) => RAlg f a -> Term f :-> a
para f = hsnd . cata run
    where run t = Term (hfmap hfst t) :&: f t

-- | This type represents monadic r-algebras over monad @m@ and
-- functor @f@ and with domain @a@.
type RAlgM m f a = NatM m (f (Term f :&: a)) a

-- | This function constructs a monadic paramorphism from the given
-- monadic r-algebra
paraM :: (HTraversable f, Monad m) => 
         RAlgM m f a -> NatM m(Term f)  a
paraM f = liftM hsnd . cataM run
    where run t = do
            a <- f t
            return (Term (hfmap hfst t) :&: a)

--------------------------------
-- R-Coalgebras & Apomorphisms --
--------------------------------

-- | This type represents r-coalgebras over functor @f@ and with
-- domain @a@.
type RCoalg f a = a :-> f ((Term f) :+: a)

-- | This function constructs an apomorphism from the given
-- r-coalgebra.
apo :: forall f a . (HFunctor f) => RCoalg f a -> a :-> Term f
apo f = run 
    where run :: a :-> Term f
          run = Term . hfmap run' . f
          run' (Inl t) = t
          run' (Inr a) = run a

-- | This type represents monadic r-coalgebras over monad @m@ and
-- functor @f@ with domain @a@.

type RCoalgM m f a = NatM m a (f ((Term f) :+: a))

-- | This function constructs a monadic apomorphism from the given
-- monadic r-coalgebra.
apoM :: forall f m a . (HTraversable f, Monad m) =>
        RCoalgM m f a -> NatM m a (Term f)
apoM f = run 
    where run :: NatM m a (Term f)
          run a = do
            t <- f a
            t' <- hmapM run' t
            return $ Term t'
          run' (Inl t) = return t
          run' (Inr a) = run a


-----------------------------------
-- CV-Coalgebras & Futumorphisms --
-----------------------------------


-- | This type represents cv-coalgebras over functor @f@ and with domain
-- @a@.

type CVCoalg f a = a :-> f (Context f a)


-- | This function constructs the unique futumorphism from the given
-- cv-coalgebra to the term algebra.

futu :: forall f a . HFunctor f => CVCoalg f a -> a :-> Term f
futu coa = ana run . Hole
    where run :: Coalg f (Context f a)
          run (Hole a) = coa a
          run (Term v) = v


-- | This type represents monadic cv-coalgebras over monad @m@ and
-- functor @f@, and with domain @a@.

type CVCoalgM m f a = NatM m a (f (Context f a))

-- | This function constructs the unique monadic futumorphism from the
-- given monadic cv-coalgebra to the term algebra.
futuM :: forall f a m . (HTraversable f, Monad m) =>
         CVCoalgM m f a -> NatM m a (Term f)
futuM coa = anaM run . Hole
    where run :: CoalgM m f (Context f a)
          run (Hole a) = coa a
          run (Term v) = return v