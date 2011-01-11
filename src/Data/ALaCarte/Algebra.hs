{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Algebra
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines the notion of algebras.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Algebra (
      -- * Algebras
      Alg,
      freeAlgHom,
      algHom,
      algHom',
      applyCxt,
      
      -- * Monadic Algebras
      AlgM,
      algM,
      freeAlgHomM,
      algHomM,
      algHomM',

      -- * Term Homomorphisms
      CxtFun,
      SigFun,
      TermHom,
      termHom,
      compTermHom,
      applySigFun,
      compSigFun,
      termAlg,
      compAlg,

      -- * Monadic Term Homomorphisms
      CxtFunM,
      SigFunM,
      TermHomM,
      SigFunM',
      TermHomM',
      sigFunM,
      termAlg',
      termAlgM,
      termHomM,
      termHomM',
      applySigFunM,
      applySigFunM',
      compTermHomM,
      compSigFunM,
      compAlgM,
      compAlgM',

      -- * Coalgebras      
      Coalg,
      coalgHom,
      CoalgM,
      coalgHomM
    ) where

import Data.ALaCarte.Term
import Data.Traversable
import Control.Monad hiding (sequence, mapM)

import Prelude hiding (sequence, mapM)



{-| This type represents an algebra over a functor @f@ and domain
@a@. -}

type Alg f a = f a -> a

freeAlgHom :: forall f h a b . (Functor f) =>
              Alg f b -> (a -> b) -> Cxt h f a -> b
freeAlgHom f g = run
    where run :: Cxt h f a -> b
          run (Hole v) = g v
          run (Term c) = f $ fmap run c

{-| This function folds the given term using the given fold
function. This is the unique homomorphism @Term f -> a@ from the
initial algebra @Term f@ to the given algebra of type @f a -> a@. -}

algHom :: forall f a . (Functor f) =>
          Alg f a -> Term f -> a 
-- algHom f = freeAlgHom f undefined
-- the above definition is safe since terms do not contain holes
--
-- a direct implementation:
algHom f = run 
    where run :: Term f -> a
          run (Term t) = f (fmap run t)

{-| This function applies the given algebra recursively to each
subcontext of the given context. -}

algHom' :: (Functor f) => Alg f a -> Cxt h f a -> a
algHom' f = freeAlgHom f id


{-| This function applies a whole context into another context. -}

applyCxt :: (Functor f) => Context f (Cxt h f a) -> Cxt h f a
applyCxt = algHom' Term


{-| This type represents a monadic algebra. It is similar to 'Alg' but
the return type is monadic.  -}

type AlgM m f a = f a -> m a 


algM :: (Traversable f, Monad m) => AlgM m f a -> Alg f (m a)
algM f x = sequence x >>= f

freeAlgHomM :: forall h f a m b. (Traversable f, Monad m) =>
               AlgM m f b -> (a -> m b) -> Cxt h f a -> m b
-- freeAlgHomM alg var = freeAlgHom (algM alg) var
freeAlgHomM algm var = run
    where run :: Cxt h f a -> m b
          run (Hole x) = var x
          run (Term x) = mapM run x >>= algm

{-| This is a monadic version of 'foldTerm'.  -}

algHomM :: forall f m a. (Traversable f, Monad m) => AlgM m f a -> Term f -> m a 
-- algHomM = algHom . algM
algHomM algm = run
    where run :: Term f -> m a
          run (Term x) = mapM run x >>= algm


{-| This function applies the given monadic algebra recursively to
each subcontext of the given context. -}

algHomM' :: forall h f a m . (Traversable f, Monad m)
            => AlgM m f a -> Cxt h f a -> m a
-- algHomM' f = freeAlgHom (\x -> sequence x >>= f) return
algHomM' f = run
    where run :: Cxt h f a -> m a
          run (Hole x) = return x
          run (Term x) = mapM run x >>= f


{-| This type represents context function. -}

type CxtFun f g = forall a h. Cxt h f a -> Cxt h g a

{-| This type represents uniform signature function
specification.-}

type SigFun f g = forall a. f a -> g a


{-| This type represents a term algebra. -}

type TermHom f g = SigFun f (Context g)

{-| This function constructs the unique term homomorphism from the
initial term algebra to the given term algebra. -}

termHom :: (Functor f, Functor g) => TermHom f g -> CxtFun f g
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (Cxt h g b) -> Context g (Cxt h g b)) -> Cxt h f b -> Cxt h g b
-- would achieve the same. The given type is chosen for clarity.
termHom _ (Hole b) = Hole b
termHom f (Term t) = applyCxt . f . fmap (termHom f) $ t

{-| This function composes two term algebras
-}

compTermHom :: (Functor g, Functor h) => TermHom g h -> TermHom f g -> TermHom f h
-- Note: The rank 2 type polymorphism is not necessary. Alternatively, also the type
-- (Functor f, Functor g) => (f (Cxt h g b) -> Context g (Cxt h g b))
-- -> (a -> Cxt h f b) -> a -> Cxt h g b
-- would achieve the same. The given type is chosen for clarity.

compTermHom f g = termHom f . g


{-| This function composes a term algebra with an algebra. -}

compAlg :: (Functor g) => Alg g a -> TermHom f g -> Alg f a
compAlg alg talg = algHom' alg . talg


{-| This function applies a signature function to the
given context. -}

applySigFun :: (Functor f, Functor g) => SigFun f g -> CxtFun f g
applySigFun f = termHom $ termAlg $ f

{-| This function composes two signature functions.  -}

compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g


{-| Lifts the given signature function to the canonical term algebra.
-}

termAlg :: (Functor g) => SigFun f g -> TermHom f g
termAlg f = simpCxt . f

{-|
  This type represents monadic context function.
-}
type CxtFunM m f g = forall a h. Cxt h f a -> m (Cxt h g a)

{-| This type represents monadic signature functions. -}

type SigFunM m f g = forall a. f a -> m (g a)

{-| This type represents monadic signature functions.  It is similar
to 'SigFunM' but has monadic values also in the domain. -}

type SigFunM' m f g = forall a. f (m a) -> m (g a)

{-| This type represents monadic term algebras.  -}

type TermHomM m f g = SigFunM m f (Context g)

{-| This type represents monadic term algebras. It is similar to
'TermHomM' but has monadic values also in the domain. -}

type TermHomM' m f g = SigFunM' m f (Context g)


{-| This function lifts the given signature function to a monadic
signature function. Note that term algebras are instances of signature
functions. Hence this function also applies to term algebras. -}

sigFunM :: (Monad m) => SigFun f g -> SigFunM m f g
sigFunM f = return . f


{-| This function lifts the give monadic signature function to a
monadic term algebra. -}

termAlg' :: (Functor f, Functor g, Monad m) => SigFunM m f g -> TermHomM m f g
termAlg' f = liftM  (Term . fmap Hole) . f

{-| This function lifts the given signature function to a monadic term
algebra. -}

termAlgM :: (Functor g, Monad m) => SigFun f g -> TermHomM m f g
termAlgM f = sigFunM $ termAlg f


{-| This function constructs the unique monadic homomorphism from the
initial term algebra to the given term algebra. -}

termHomM :: forall f g m . (Traversable f, Functor g, Monad m)
         => TermHomM m f g -> CxtFunM m f g
termHomM f = run
    where run :: Cxt h f a -> m (Cxt h g a)
          run (Hole b) = return $ Hole b
          run (Term t) = liftM applyCxt . (>>= f) . mapM run $ t

{-| This function constructs the unique monadic homomorphism from the
initial term algebra to the given term algebra. -}

termHomM' :: forall f g m . (Traversable f, Functor g, Monad m)
          => TermHomM' m f g -> CxtFunM m f g
termHomM' f = run 
    where run :: Cxt h f a -> m (Cxt h g a)
          run (Hole b) = return $ Hole b
          run (Term t) = liftM applyCxt . f . fmap run $ t


{-| This function applies the given monadic signature function to the
given context -}

applySigFunM :: (Traversable f, Functor g, Monad m) => SigFunM m f g -> CxtFunM m f g
applySigFunM f = termHomM $ termAlg' $ f

{-| This function applies the given monadic signature function to the
given context -}

applySigFunM' :: forall f g m . (Traversable f, Functor g, Monad m)
              => SigFunM' m f g -> CxtFunM m f g
applySigFunM' f = run 
    where run :: Cxt h f a -> m (Cxt h g a)
          run (Hole b) = return $ Hole b
          run (Term t) = liftM Term . f . fmap run $ t

{-| This function composes two monadic term algebras. -}

compTermHomM :: (Traversable g, Functor h, Monad m)
            => TermHomM m g h -> TermHomM m f g -> TermHomM m f h
compTermHomM f g a = g a >>= termHomM f


{-| This function composes a monadic term algebra with a monadic algebra -}

compAlgM :: (Traversable g, Monad m) => AlgM m g a -> TermHomM m f g -> AlgM m f a
compAlgM alg talg c = algHomM' alg =<< talg c

{-| This function composes a monadic term algebra with a monadic algebra -}

compAlgM' :: forall g f m a. (Traversable g, Monad m) => AlgM m g a -> TermHom f g -> AlgM m f a
compAlgM' alg talg = algHomM' alg . talg


{-| This function composes two monadic signature functions.  -}

compSigFunM :: (Monad m) => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g a = g a >>= f


type Coalg f a = a -> f a

{-| This function unfolds the given value to a term using the given
unravelling function. This is the unique homomorphism @a -> Term f@
from the given coalgebra of type @a -> f a@ to the final coalgebra
@Term f@. -}

coalgHom :: forall a f . Functor f
         => Coalg f a -> a -> Term f
coalgHom f = run
    where run :: a -> Term f
          run t = Term $ fmap run (f t)

type CoalgM m f a = a -> m (f a)

{-| This function unfolds the given value to a term using the given
monadic unravelling function. This is the unique homomorphism @a ->
Term f@ from the given coalgebra of type @a -> f a@ to the final
coalgebra @Term f@. -}

coalgHomM :: forall a m f. (Traversable f, Monad m)
          => CoalgM m f a -> a -> m (Term f)
coalgHomM f = run 
    where run :: a -> m (Term f)
          run t = liftM Term $ f t >>= mapM run