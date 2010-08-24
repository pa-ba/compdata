{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
             UndecidableInstances, FlexibleInstances, FlexibleContexts,
             ScopedTypeVariables, FunctionalDependencies, EmptyDataDecls,
             GADTs, KindSignatures, RankNTypes, TypeSynonymInstances#-}
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
     (:<:)(..),
     inject,
     deepInject,
     deepInject2,
     deepInject3,
     project,
     deepProject,
     (:*:)(..),
     liftP,
     constP,
     stripP,
     project'
    ) where

import Prelude hiding (and, foldr, sequence, foldl, foldr1, foldl1, mapM)
import Control.Applicative
import Control.Monad (liftM)

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

applyCxt :: (Functor f, f :<: g) => Cxt h' f v -> (v -> Cxt h g a) -> Cxt h g a
applyCxt c f = injectCxt $ fmap f c

applyCxt' :: (Functor f, f :<: g, Ord v) => Cxt h' f v -> Map v (Cxt h g a) -> Cxt h g a
applyCxt' c m = applyCxt c (fromJust . (`Map.lookup`  m))



instance Functor f => Functor (Cxt h f) where
    fmap f (Hole v) = Hole (f v)
    fmap f (Term t) = Term (fmap (fmap f) t)

instance Functor f => Monad (Context f) where
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

compTermAlg :: (Functor h, Functor g) => TermAlg g h -> TermAlg f g -> TermAlg f h
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

algHom :: Functor f => Alg f a -> Term f -> a 
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

-- |The subsumption relation.
class (Functor sub, Functor sup) => (:<:) sub sup where
  inj :: sub a -> sup a
  proj :: sup a -> Maybe (sub a)

instance Functor f => (:<:) f f where
  inj = id
  proj x = Just x

instance (Functor f, Functor g) => (:<:) f (f :+: g) where
    inj = Inl
    proj (Inl x) = Just x
    proj (Inr _) = Nothing

instance (Functor f, Functor g, Functor h, f :<: g) => (:<:) f (h :+: g) where
    inj = Inr . inj
    proj (Inr x) = proj x
    proj (Inl _) = Nothing

-- |Project a sub term from a compound term.
project :: (g :<:f) => Cxt h f a -> Maybe (g (Cxt h f a))
project (Hole _) = Nothing
project (Term t) = proj t

-- |Project a sub term recursively from a term.
deepProject :: (Traversable f, g :<: f) => Cxt h f a -> Maybe (Cxt h g a)
deepProject = applySigFunM proj

-- |Inject a term into a compound term.
inject :: (g :<: f) => g (Cxt h f a) -> Cxt h f a
inject = Term . inj


{-| This function injects a whole context into another context. -}

injectCxt :: (Functor f, g :<: f) => Cxt h' g (Cxt h f a) -> Cxt h f a
injectCxt = algHom' inject


{-| Deep injection function.  -}

deepInject  :: (g :<: f) => Cxt h g a -> Cxt h f a
deepInject = applySigFun inj

{-| This is a variant of 'inj' for binary sum signatures.  -}

inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a -> g a
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

-- |A recursive version of 'inj2'.
deepInject2 :: (f1 :<: g, f2 :<: g) => Cxt h (f1 :+: f2) a -> Cxt h g a
deepInject2 = applySigFun inj2

{-| This is a variant of 'inj' for ternary sum signatures.  -}

inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a -> g a
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |A recursive version of 'inj3'.
deepInject3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => Cxt h (f1 :+: f2 :+: f3) a -> Cxt h g a
deepInject3 =  applySigFun inj3


infixr 7 :*:

-- |Data type defining products.
data (f :*: a) e = f e :*: a


{-| Instances of this class provide functions to strip a product from
a functor -}

class ProjectP f g | f -> g where
    {-| This function is intended to strip products from a
      functor. Here @g@ is supposed to be the same as functor @f@ but
      without a product -}
    
    projectP :: f a -> g a

instance ProjectP (f :*: c) f where
    projectP (v :*: _) = v

instance ProjectP g g' =>  ProjectP (f :*: c :+: g) (f :+: g') where
    projectP (Inl (v :*: _)) = Inl v
    projectP (Inr v) = Inr $ projectP v

{-| This function transforms a function with a domain constructed from
a functor to a function with a domain constructed with the same
functor but with an additional product. -}

liftP :: (ProjectP f f') => (f' a -> b) -> f a -> b
liftP f v = f (projectP v)
    
{-| This function strips the products from a term over a
functor with products. -}

stripP :: (ProjectP f g, Functor g, Functor f) => Cxt h f a -> Cxt h g a
stripP = applySigFun projectP



instance (Functor f) => Functor (f :*: a) where
    fmap f (v :*: c) = fmap f v :*: c

instance (Foldable f) => Foldable (f :*: a) where
    fold (v :*: _) = fold v
    foldMap f (v :*: _) = foldMap f v
    foldr f e (v :*: _) = foldr f e v
    foldl f e (v :*: _) = foldl f e v
    foldr1 f (v :*: _) = foldr1 f v
    foldl1 f (v :*: _) = foldl1 f v

instance (Traversable f) => Traversable (f :*: a) where
    traverse f (v :*: c) = liftA (:*: c) (traverse f v)
    sequenceA (v :*: c) = liftA (:*: c)(sequenceA v)
    mapM f (v :*: c) = liftM (:*: c) (mapM f v)
    sequence (v :*: c) = liftM (:*: c) (sequence v)


class InjectP f g c | g -> c, g -> f where
    injectP :: c -> f a -> g a

instance InjectP  f (f :*: c) c where
    injectP c v = v :*: c

instance InjectP g g' c =>  InjectP (f :+: g) (f :*: c :+: g')  c where
    injectP c (Inl v) = Inl (v :*: c)
    injectP c (Inr v) = Inr $ injectP c v

{-| This function annotates each sub term of the given term
with the given value (of type a). -}

constP :: (InjectP f g c, Functor f, Functor g)
       => c -> Cxt h f a -> Cxt h g a
constP c = applySigFun (injectP c)


{-| This function is similar to 'project' but applies to signatures
with a product which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (ProjectP f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM projectP $ project v

