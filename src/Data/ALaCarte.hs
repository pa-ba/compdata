{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             UndecidableInstances, FlexibleInstances, FlexibleContexts,
             ScopedTypeVariables, FunctionalDependencies, EmptyDataDecls,
             GADTs, KindSignatures, RankNTypes, TypeSynonymInstances, TypeFamilies#-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines the infrastructure necessary to use Wouter Swierstra's
-- Functional Pearl: /Data types a la carte/.
--
--------------------------------------------------------------------------------
module Data.ALaCarte
    (
     Term,
     Hole,
     NoHole,
     Nothing,
     Cxt(..),
     Context,
     Alg,
     AlgM,
     TermAlg,
     TermAlgM,
     CxtFun,
     CxtFunM,
     SigFun,
     SigFunM,
     algM,
     unTerm,
     freeAlgHom,
     algHom',
     algHomM',
     injectCxt,
     termAlg,
     termAlg',
     termAlgM,
     sigFunM,
     compTermAlg,
     compSigFun,
     compTermAlgM,
     compSigFunM,
     termHom,
     termHomM,
     applySigFun,
     applySigFunM,
     applyCxt,
     applyCxt',
     algHom,
     algHomM,
     coalgHom,
     (:+:)(..),
     (:++:),
     NilF,
     (:<:)(..),
     inject,
     deepInject,
     project,
     deepProject,
    ) where

import Prelude hiding (and, foldr, sequence, foldl, foldr1, foldl1, mapM)
import Control.Applicative
import Control.Monad hiding (sequence, mapM)

import Data.Traversable 
import Data.Foldable 
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

{-| Phantom type that signals that a 'Cxt' might contain holes.  -}

data Hole

{-| Phantom type that signals that a 'Cxt' does not contain holes.
-}

data NoHole

{-| This data type represents contexts over a signature. Contexts are
terms containing zero or more holes. The first type parameter is
supposed to be one of the phantom types 'Hole' and 'NoHole'. The
second parameter is the signature of the context. The third parameter
is the type of the holes. -}

data Cxt :: * -> (* -> *) -> * -> * where
            Term :: f (Cxt h f a) -> Cxt h f a
            Hole :: a -> Cxt Hole f a

type Context = Cxt Hole

{-| This type represents an algebra over a functor @f@ and domain
@a@. -}

type Alg f a = f a -> a

freeAlgHom :: (Functor f) => Alg f b -> (a -> b) -> Cxt h f a -> b
freeAlgHom _ g (Hole v) = g v
freeAlgHom f g (Term c) = f $ fmap (freeAlgHom f g) c

{-| This function applies the given algebra recursively to each
subcontext of the given context. -}

algHom' :: (Functor f) => Alg f a -> Cxt h f a -> a
algHom' f = freeAlgHom f id

{-| This type represents a monadic algebra. It is similar to 'Alg' but
the return type is monadic.  -}

type AlgM m f a = f a -> m a 


{-| This function applies the given monadic algebra recursively to
each subcontext of the given context. -}

algHomM' :: (Traversable f, Monad m) => AlgM m f a -> Cxt h f a -> m a
algHomM' f = freeAlgHom (\x -> sequence x >>= f) return


{-| This function applies the given context with hole type @a@ to a
family @f@ of contexts (possibly terms) indexed by @a@. That is, each
hole @h@ is replaced by the context @f h@. -}

applyCxt :: (Functor f, Functor g, f :<: g) => Cxt h' f v -> (v -> Cxt h g a) -> Cxt h g a
applyCxt c f = injectCxt $ fmap f c

applyCxt' :: (Functor f, Functor g, f :<: g, Ord v) => Cxt h' f v -> Map v (Cxt h g a) -> Cxt h g a
applyCxt' c m = applyCxt c (fromJust . (`Map.lookup`  m))



instance Functor f => Functor (Cxt h f) where
    fmap f (Hole v) = Hole (f v)
    fmap f (Term t) = Term (fmap (fmap f) t)

instance (Functor f) => Monad (Context f) where
    return = Hole
    (>>=) = applyCxt

instance (Foldable f) => Foldable (Cxt h f) where
    foldr op e (Hole a) = a `op` e
    foldr op e (Term t) = foldr op' e t
        where op' c a = foldr op a c

    foldl op e (Hole a) = e `op` a
    foldl op e (Term t) = foldl op' e t
        where op' a c = foldl op a c

    fold (Hole a) = a
    fold (Term t) = foldMap fold t

    foldMap f (Hole a) = f a
    foldMap f (Term t) = foldMap (foldMap f) t

instance (Traversable f) => Traversable (Cxt h f) where
    traverse f (Hole a) = Hole <$> f a
    traverse f (Term t) = Term <$> traverse (traverse f) t
                          
    sequenceA (Hole a) = Hole <$> a
    sequenceA (Term t) = Term <$> traverse sequenceA t

    mapM f (Hole a) = liftM Hole $ f a
    mapM f (Term t) = liftM Term $ mapM (mapM f) t

    sequence (Hole a) = liftM Hole $ a
    sequence (Term t) = liftM Term $ mapM sequence t


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
termHom f (Term t) = injectCxt . f . fmap (termHom f) $ t

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

{-|
  This type represents monadic context function.
-}
type CxtFunM m f g = forall a h. Cxt h f a -> m (Cxt h g a)


{-| Lifts the given signature function to the canonical term algebra.
-}

termAlg :: (Functor g) => SigFun f g -> TermAlg f g
termAlg f = Term . fmap Hole . f

{-| This type represents monadic signature functions. -}

type SigFunM m f g = forall a. f a -> m (g a)


{-| This function lifts the given signature function to a monadic
signature function. Note that term algebras are instances of signature
functions. Hence this function also applies to term algebras. -}

sigFunM :: (Monad m) => SigFun f g -> SigFunM m f g
sigFunM f = return . f

{-| This type represents monadic term algebras.  -}

type TermAlgM m f g = SigFunM m f (Context g)

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
termHomM f (Term t) = liftM injectCxt . (>>= f) . sequence . fmap (termHomM f) $ t

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

{-| Phantom type used to define 'Term'.  -}

data Nothing

instance Eq Nothing where
instance Ord Nothing where
instance Show Nothing where

{-| A term is a context with no holes.  -}

type Term f = Cxt NoHole f Nothing

{-| This function unravels the given term at the topmost layer.  -}

unTerm :: Term f -> f (Term f)
unTerm (Term t) = t

{-| This function unfolds the given value to a term using the given
unravelling function. This is the unique homomorphism @a -> Term f@
from the given coalgebra of type @a -> f a@ to the final coalgebra
@Term f@. -}

coalgHom :: Functor f => (a -> f a ) -> a -> Term f
coalgHom f t = Term $ (fmap (coalgHom f)  (f t))

{-| This function folds the given term using the given fold
function. This is the unique homomorphism @Term f -> a@ from the
initial algebra @Term f@ to the given algebra of type @f a -> a@. -}

algHom :: (Functor f) => Alg f a -> Term f -> a 
algHom f = freeAlgHom f undefined
-- the above definition is safe since terms do not contain holes
--
-- a direct implementation:
-- foldTerm f (Term t) = f (fmap (foldTerm f) t)


algM :: (Traversable f, Monad m) => AlgM m f a -> Alg f (m a)
algM f x = sequence x >>= f


{-| This is a monadic version of 'foldTerm'.  -}

algHomM :: (Traversable f, Monad m) => AlgM m f a -> Term f -> m a 
algHomM = algHom . algM

infixr 6 :+:
infixr 5 :++:

data NilF :: * -> * 


type family (:++:) (f :: * -> *) (g :: * -> *) :: * -> *

type instance (:++:) NilF f = f
type instance (:++:) (f :+: f') g = f :+: (f' :++: g)

-- |Data type defining coproducts.
data (f :+: g) e = Inl (f e)
                 | Inr (g e)

instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (Inl e) = Inl (fmap f e)
    fmap f (Inr e) = Inr (fmap f e)

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
    foldr f b (Inl e) = foldr f b e
    foldr f b (Inr e) = foldr f b e

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
    traverse f (Inl e) = Inl <$> traverse f e
    traverse f (Inr e) = Inr <$> traverse f e

instance Functor NilF where
    fmap = undefined


instance Foldable NilF where

instance Traversable NilF where


class Elem f g where
  inj' :: f a -> g a
  proj' :: g a -> Maybe (f a)

instance Elem f (f :+: g) where
    inj' = Inl
    proj' (Inl v) = Just v
    proj' (Inr _) = Nothing

instance (Elem f g) => Elem f (f' :+: g) where
    inj' = Inr . inj'
    proj' (Inl _) = Nothing
    proj' (Inr v) = proj' v

-- |The subsumption relation.
class sub :<: sup where
  inj :: sub a -> sup a
  proj :: sup a -> Maybe (sub a)

instance (:<:) f f where
    inj = id
    proj = Just
                                    
instance (:<:) NilF f where
    inj = undefined
    proj _ = undefined

instance (Elem f g, f' :<: g) => (:<:) (f :+: f') g where
  inj (Inl v) = inj' v
  inj (Inr v) = inj v

  proj v = (Inl <$> proj' v) `mplus` (Inr <$> proj v)

-- |Project a sub term from a compound term.
project :: (g :<: f) => Cxt h f a -> Maybe (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = proj t

-- |Project a sub term recursively from a term.
deepProject :: (Traversable f, Functor g, g :<: f) => Cxt h f a -> Maybe (Cxt h g a)
deepProject = applySigFunM proj

-- |Inject a term into a compound term.
inject :: (g :<: f) => g (Cxt h f a) -> Cxt h f a
inject = Term . inj


{-| This function injects a whole context into another context. -}

injectCxt :: (Functor g, g :<: f) => Cxt h' g (Cxt h f a) -> Cxt h f a
injectCxt = algHom' inject


{-| Deep injection function.  -}

deepInject  :: (Functor g, Functor f, g :<: f) => Cxt h g a -> Cxt h f a
deepInject = applySigFun inj

