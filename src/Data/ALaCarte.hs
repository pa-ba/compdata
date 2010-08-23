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
     Cxt(..),
     Alg,
     unTerm,
     foldCxt,
     foldCxtM,
     injectCxt,
     transN,
     transN',
     transM,
     transNM,
     compTransN,
     compTransU,
     compTransNM,
     compTransUM,
     applyTransN,
     applyTransU,
     applyTransNM,
     applyTransUM,
     applyCxt,
     foldTerm,
     foldTermM,
     unfoldTerm,
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
import Data.Traversable 
import Data.Foldable 
import Control.Monad (liftM)

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


{-| This type represents an algebra over a functor @f@ and domain
@a@. -}

type Alg f a = f a -> a

foldCxt' :: (Functor f) => Alg f b -> (a -> b) -> Cxt h f a -> b
foldCxt' _ g (Hole v) = g v
foldCxt' f g (Term c) = f $ fmap (foldCxt' f g) c

{-| This function applies the given algebra recursively to each
subcontext of the given context. -}

foldCxt :: (Functor f) => Alg f a -> Cxt h f a -> a
foldCxt f = foldCxt' f id

{-| This type represents a monadic algebra. It is similar to 'Alg' but
the return type is monadic.  -}

type AlgM m f a = f a -> m a 


{-| This function applies the given monadic algebra recursively to
each subcontext of the given context. -}

foldCxtM :: (Traversable f, Monad m) => AlgM m f a -> Cxt h f a -> m a
foldCxtM f = foldCxt' (\x -> sequence x >>= f) return


{-| This function applies the given context with hole type @a@ to a
family @f@ of contexts (possibly terms) indexed by @a@. That is, each
hole @h@ is replaced by the context @f h@. -}

applyCxt :: (Functor f, f :<: g) => Cxt h' f a -> (a -> Cxt h g b) -> Cxt h g b
applyCxt c f = injectCxt $ fmap f c

instance Functor f => Functor (Cxt h f) where
    fmap f (Hole v) = Hole (f v)
    fmap f (Term t) = Term (fmap (fmap f) t)

instance Functor f => Monad (Cxt Hole f) where
    return = Hole
    (>>=) = applyCxt


{-| This type represents context transformations. -}

type TransC f g = forall a h. Cxt h f a -> Cxt h g a

{-| This type represents uniform signature transformation
specification.-}

type TransU f g = forall a. f a -> g a


{-| This type represents a non-uniform signature transformation. -}

type TransN f g = TransU f (Cxt Hole g)

{-| This function applies a non-uniform signature transformation to
the given context.  -}

applyTransN :: (Functor f, Functor g) => TransN f g -> TransC f g
applyTransN _ (Hole b) = Hole b
applyTransN f (Term t) = injectCxt . f . fmap (applyTransN f) $ t

{-| This function composes two non-uniform signature transformation
-}

compTransN :: (Functor h, Functor g) => TransN g h -> TransN f g -> TransN f h
compTransN f g = applyTransN f . g

{-| This function applies a uniform signature transformation to the
given context. -}

applyTransU :: (Functor f, Functor g) => TransU f g -> TransC f g
applyTransU f = applyTransN . transN $ f

{-| This function composes two uniform signature transformations.  -}

compTransU :: TransU g h -> TransU f g -> TransU f h
compTransU f g = f . g

{-|
  This type represents monadic context transformations.
-}
type TransCM m f g = forall a h. Cxt h f a -> m (Cxt h g a)


{-| Lifts the given uniform signature transformation to a non-uniform
signature transformation.  -}

transN :: (Functor g) => TransU f g -> TransN f g
transN f = Term . fmap Hole . f

{-| This type represents monadic uniform signature transformations. -}

type TransUM m f g = forall a. f a -> m (g a)


{-| This function lifts the given (uniform) signature transformation
to a monadic (uniform) signature transformation. -}

transM :: (Monad m) => TransU f g -> TransUM m f g
transM f = return . f

{-| This type represents monadic non-uniform signature transformations.  -}

type TransNM m f g = TransUM m f (Cxt Hole g)

{-| This function lifts the give monadic uniform signature
transformation to a monadic non-uniform signature transformation. -}

transN' :: (Functor f, Functor g, Monad m) => TransUM m f g -> TransNM m f g
transN' f = liftM  (Term . fmap Hole) . f

{-| This function lifts the given uniform signature transformation to
a monadic non-uniform signature transformation. -}

transNM :: (Functor g, Monad m) => TransU f g -> TransNM m f g
transNM f = transM $ transN f

{-| This function applies the given monadic non-uniform signature
transformation the given context. -}
applyTransNM :: (Traversable f, Functor g, Monad m) => TransNM m f g -> TransCM m f g
applyTransNM _ (Hole b) = return $ Hole b
applyTransNM f (Term t) = liftM injectCxt . (>>= f) . sequence . fmap (applyTransNM f) $ t

{-| This function applies the given monadic uniform signature
transformation to the given context -}

applyTransUM :: (Traversable f, Functor g, Monad m) => TransUM m f g -> TransCM m f g
applyTransUM f = applyTransNM . transN' $ f

{-| This function composes two monadic non-uniform signature
transformations. -}

compTransNM :: (Traversable g, Functor h, Monad m)
            => TransNM m g h -> TransNM m f g -> TransNM m f h
compTransNM f g a = g a >>= applyTransNM f

{-| This function composes two monadic uniform signature
transformations.  -}

compTransUM :: (Monad m) => TransUM m g h -> TransUM m f g -> TransUM m f h
compTransUM f g a = g a >>= f

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

unfoldTerm :: Functor f => (a -> f a ) -> a -> Term f
unfoldTerm f t = Term $ (fmap (unfoldTerm f)  (f t))

{-| This function folds the given term using the given fold
function. This is the unique homomorphism @Term f -> a@ from the
initial algebra @Term f@ to the given algebra of type @f a -> a@. -}

foldTerm :: Functor f => Alg f a -> Term f -> a 
foldTerm f = foldCxt' f undefined
-- the above definition is safe since terms do not contain holes
--
-- a direct implementation:
-- foldTerm f (Term t) = f (fmap (foldTerm f) t)

{-| This is a monadic version of 'foldTerm'.  -}

foldTermM :: (Traversable f, Monad m) => AlgM m f a -> Term f -> m a 
foldTermM f = foldTerm (\x -> sequence x >>= f)

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
deepProject = applyTransUM proj

-- |Inject a term into a compound term.
inject :: (g :<: f) => g (Cxt h f a) -> Cxt h f a
inject = Term . inj


{-| This function injects a whole context into another context. -}

injectCxt :: (Functor f, g :<: f) => Cxt h' g (Cxt h f a) -> Cxt h f a
injectCxt = foldCxt inject


{-| Deep injection function.  -}

deepInject  :: (g :<: f) => Cxt h g a -> Cxt h f a
deepInject = applyTransU inj

{-| This is a variant of 'inj' for binary sum signatures.  -}

inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a -> g a
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

-- |A recursive version of 'inj2'.
deepInject2 :: (f1 :<: g, f2 :<: g) => Cxt h (f1 :+: f2) a -> Cxt h g a
deepInject2 = applyTransU inj2

{-| This is a variant of 'inj' for ternary sum signatures.  -}

inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a -> g a
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |A recursive version of 'inj3'.
deepInject3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => Cxt h (f1 :+: f2 :+: f3) a -> Cxt h g a
deepInject3 =  applyTransU inj3


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
stripP = applyTransU projectP



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
constP c = applyTransU (injectP c)


{-| This function is similar to 'project' but applies to signatures
with a product which is then ignored. -}
-- bug in type checker? below is the inferred type, however, the type checker
-- rejects it.
-- project' :: (ProjectP f g, f :<: f1) => Cxt h f1 a -> Maybe (g (Cxt h f1 a))
project' v = liftM projectP $ project v

