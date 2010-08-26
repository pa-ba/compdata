{-# LANGUAGE GADTs, RankNTypes #-}

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

      -- * Term Algebras
      CxtFun,
      SigFun,
      TermAlg,
      termHom,
      compTermAlg,
      applySigFun,
      compSigFun,
      termAlg,

      -- * Monadic Term Algebras
      CxtFunM,
      SigFunM,
      TermAlgM,
      sigFunM,
      termAlg',
      termAlgM,
      termHomM,
      applySigFunM,
      compTermAlgM,
      compSigFunM,

      -- * Coalgebras      
      coalgHom
    ) where

import Data.ALaCarte.Term
import Data.Traversable
import Control.Monad hiding (sequence)

import Prelude hiding (sequence)



{-| This type represents an algebra over a functor @f@ and domain
@a@. -}

type Alg f a = f a -> a

freeAlgHom :: (Functor f) => Alg f b -> (a -> b) -> Cxt h f a -> b
freeAlgHom _ g (Hole v) = g v
freeAlgHom f g (Term c) = f $ fmap (freeAlgHom f g) c

{-| This function folds the given term using the given fold
function. This is the unique homomorphism @Term f -> a@ from the
initial algebra @Term f@ to the given algebra of type @f a -> a@. -}

algHom :: (Functor f) => Alg f a -> Term f -> a 
algHom f = freeAlgHom f undefined
-- the above definition is safe since terms do not contain holes
--
-- a direct implementation:
-- foldTerm f (Term t) = f (fmap (foldTerm f) t)

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

freeAlgHomM :: (Traversable f, Monad m) => AlgM m f b -> (a -> m b) -> Cxt h f a -> m b
freeAlgHomM alg var = freeAlgHom (algM alg) var

{-| This is a monadic version of 'foldTerm'.  -}

algHomM :: (Traversable f, Monad m) => AlgM m f a -> Term f -> m a 
algHomM = algHom . algM


{-| This function applies the given monadic algebra recursively to
each subcontext of the given context. -}

algHomM' :: (Traversable f, Monad m) => AlgM m f a -> Cxt h f a -> m a
algHomM' f = freeAlgHom (\x -> sequence x >>= f) return



{-| This type represents context function. -}

type CxtFun f g = forall a h. Cxt h f a -> Cxt h g a

{-| This type represents uniform signature function
specification.-}

type SigFun f g = forall a. f a -> g a


{-| This type represents a term algebra. -}

type TermAlg f g = SigFun f (Context g)

{-| This function constructs the unique term homomorphism from the
initial term algebra to the given term algebra. -}

termHom :: (Functor f, Functor g) => TermAlg f g -> CxtFun f g
termHom _ (Hole b) = Hole b
termHom f (Term t) = applyCxt . f . fmap (termHom f) $ t

{-| This function composes two term algebras
-}

compTermAlg :: (Functor g, Functor h) => TermAlg g h -> TermAlg f g -> TermAlg f h
compTermAlg f g = termHom f . g

{-| This function applies a signature function to the
given context. -}

applySigFun :: (Functor f, Functor g) => SigFun f g -> CxtFun f g
applySigFun f = termHom . termAlg $ f

{-| This function composes two signature functions.  -}

compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g


{-| Lifts the given signature function to the canonical term algebra.
-}

termAlg :: (Functor g) => SigFun f g -> TermAlg f g
termAlg f = Term . fmap Hole . f

{-|
  This type represents monadic context function.
-}
type CxtFunM m f g = forall a h. Cxt h f a -> m (Cxt h g a)

{-| This type represents monadic signature functions. -}

type SigFunM m f g = forall a. f a -> m (g a)


{-| This type represents monadic term algebras.  -}

type TermAlgM m f g = SigFunM m f (Context g)


{-| This function lifts the given signature function to a monadic
signature function. Note that term algebras are instances of signature
functions. Hence this function also applies to term algebras. -}

sigFunM :: (Monad m) => SigFun f g -> SigFunM m f g
sigFunM f = return . f


{-| This function lifts the give monadic signature function to a
monadic term algebra. -}

termAlg' :: (Functor f, Functor g, Monad m) => SigFunM m f g -> TermAlgM m f g
termAlg' f = liftM  (Term . fmap Hole) . f

{-| This function lifts the given signature function to a monadic term
algebra. -}

termAlgM :: (Functor g, Monad m) => SigFun f g -> TermAlgM m f g
termAlgM f = sigFunM $ termAlg f

{-| This function constructs the unique monadic homomorphism from the
initial term algebra to the given term algebra. -}

termHomM :: (Traversable f, Functor g, Monad m) => TermAlgM m f g -> CxtFunM m f g
termHomM _ (Hole b) = return $ Hole b
termHomM f (Term t) = liftM applyCxt . (>>= f) . sequence . fmap (termHomM f) $ t

{-| This function applies the given monadic signature function to the
given context -}

applySigFunM :: (Traversable f, Functor g, Monad m) => SigFunM m f g -> CxtFunM m f g
applySigFunM f = termHomM . termAlg' $ f

{-| This function composes two monadic term algebras. -}

compTermAlgM :: (Traversable g, Functor h, Monad m)
            => TermAlgM m g h -> TermAlgM m f g -> TermAlgM m f h
compTermAlgM f g a = g a >>= termHomM f

{-| This function composes two monadic signature functions.  -}

compSigFunM :: (Monad m) => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g a = g a >>= f



{-| This function unfolds the given value to a term using the given
unravelling function. This is the unique homomorphism @a -> Term f@
from the given coalgebra of type @a -> f a@ to the final coalgebra
@Term f@. -}

coalgHom :: Functor f => (a -> f a ) -> a -> Term f
coalgHom f t = Term $ (fmap (coalgHom f)  (f t))
