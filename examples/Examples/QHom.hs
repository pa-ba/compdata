{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, TemplateHaskell, TypeOperators,
  ImplicitParams, GADTs, IncoherentInstances, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.QHom
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines stateful term homomorphisms. This (slightly
-- oxymoronic) notion extends per se stateless term homomorphisms with
-- a state that is maintained separately by a bottom-up or top-down
-- tree automaton.
--
--------------------------------------------------------------------------------

module Examples.QHom where

import Examples.Zippable
import Data.Comp
import Data.Comp.Show ()
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad
import Data.Comp.Derive

-- | An instance @a :< b@ means that @a@ is a component of @b@. @a@
-- can be extracted from @b@ via the method 'ex'.
class a :< b where
    ex :: b -> a
    up :: a -> b -> b

instance a :< a where
    ex = id
    up = const

instance a :< (a,b) where
    ex = fst
    up x (_,y) = (x,y)

instance (a :< b) => a :< (a',b) where
    ex = ex . snd
    up  y (x,y') = (x,up y y')

-- | This function provides access to components of the states from
-- "below".
below :: (?below :: a -> q, p :< q) => a -> p
below = ex . ?below

-- | This function provides access to components of the state from
-- "above"
above :: (?above :: q, p :< q) => p
above = ex ?above

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.
explicit :: q -> (a -> q) -> ((?above :: q, ?below :: a -> q) => b) -> b
explicit ab be x = x
    where ?above = ab
          ?below = be


-- | This type represents stateful term homomorphisms. Stateful term
-- homomorphisms have access to a state that is provided (separately)
-- by a DUTA or a DDTA (or both).
type QHom q f g = forall a . (?below :: a -> q, ?above :: q) => f a -> Context g a


-- | This type represents transition functions of deterministic
-- bottom-up tree transducers (DUTTs).

type UpTrans q f g = forall a. f (q,a) -> (q, Context g a)

-- | This function transforms DUTT transition function into an
-- algebra.

upAlg :: (Functor g)  => UpTrans q f g -> Alg f (q, Term g)
upAlg trans = fmap appCxt . trans 

-- | This function runs the given DUTT on the given term.

runUpTrans :: (Functor f, Functor g) => UpTrans q f g -> Term f -> (q, Term g)
runUpTrans = cata . upAlg

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.
runUpTrans' :: (Functor f, Functor g) => UpTrans q f g -> Context f (q,a) -> (q, Context g a)
runUpTrans' trans = run where
    run (Hole (q,a)) = (q, Hole a)
    run (Term t) = fmap appCxt $ trans $ fmap run t

-- | This function composes two DUTTs. (see TATA, Theorem 6.4.5)
compUpTrans :: (Functor f, Functor g, Functor h)
               => UpTrans q2 g h -> UpTrans q1 f g -> UpTrans (q1,q2) f h
compUpTrans t2 t1 x = ((q1,q2), c2) where
    (q1, c1) = t1 $ fmap (\((q1,q2),a) -> (q1,(q2,a))) x
    (q2, c2) = runUpTrans' t2 c1

-- | This type represents transition functions of deterministic
-- bottom-up tree acceptors (DUTAs).
type UpState f q = Alg f q

-- | This combinator runs the given DUTA on a term returning the final
-- state of the run.
runUpState :: (Functor f) => UpState f q -> Term f -> q
runUpState = cata

-- | This function combines the product DUTA of the two given DUTAs.
prodUpState :: Functor f => UpState f p -> UpState f q -> UpState f (p,q)
prodUpState sp sq t = (p,q) where
    p = sp $ fmap fst t
    q = sq $ fmap snd t


-- | This function turns constructs a DUTT from a given stateful term
-- homomorphism with the state propagated by the given DUTA.
toUpTrans :: (Functor f, Functor g) => UpState f q -> QHom q f g -> UpTrans q f g
toUpTrans alg f t = (q, c)
    where q = alg $ fmap fst t
          c =  fmap snd $ explicit q fst f t

-- | This function applies a given stateful term homomorphism with
-- a state space propagated by the given DUTA to a term.
upHom :: (Functor f, Functor g) => UpState f q -> QHom q f g -> Term f -> (q,Term g)
upHom alg h = runUpTrans (toUpTrans alg h)


-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GDUTAs) which have access
-- to an extended state space.
type GUpState f q p = forall a . (?below :: a -> p, ?above :: p, q :< p) => f a -> q

-- | This combinator turns an arbitrary DUTA into a GDUTA.
gUpState :: Functor f => UpState f q -> GUpState f q p
gUpState f = f . fmap below

-- | This combinator turns a GDUTA with the smallest possible state
-- space into a DUTA.
upState :: GUpState f q q -> UpState f q
upState f s = res
    where res = explicit res id f s

-- | This combinator runs a GDUTA on a term.
runGUpState :: Functor f => GUpState f q q -> Term f -> q
runGUpState = runUpState . upState

-- | This combinator constructs the product of two GDUTA.
prodGUpState :: (p :< pq, q :< pq)
             => GUpState f p pq -> GUpState f q pq -> GUpState f (p,q) pq
prodGUpState sp sq t = (sp t, sq t)


-- | This type represents transition functions of deterministic
-- top-down tree transducers (DDTTs).

type DownTrans q f g = forall a. (q, f a) -> Context g (q,a)

-- | This function runs the given DDTT on the given tree.
runDownTrans :: (Functor f, Functor g) => DownTrans q f g -> q -> Cxt h f a -> Cxt h g a
runDownTrans tr q t = run (q,t) where
    run (q,Term t) = appCxt $ fmap run $  tr (q, t)
    run (_,Hole a)      = Hole a

-- | This function runs the given DDTT on the given tree.
runDownTrans' :: (Functor f, Functor g) => DownTrans q f g -> q -> Cxt h f a -> Cxt h g (q,a)
runDownTrans' tr q t = run (q,t) where
    run (q,Term t) = appCxt $ fmap run $  tr (q, t)
    run (q,Hole a)      = Hole (q,a)

-- | This function composes two DDTTs. (see Z. Fülöp, H. Vogler
-- "Syntax-Directed Semantics", Theorem 3.39)
compDownTrans :: (Functor f, Functor g, Functor h)
              => DownTrans p g h -> DownTrans q f g -> DownTrans (q,p) f h
compDownTrans t2 t1 ((q,p), t) = fmap (\(p, (q, a)) -> ((q,p),a)) $ runDownTrans' t2 p (t1 (q, t))


-- | This type represents transition functions of deterministic
-- top-down tree acceptors (DDTAs).
type DownState f q = forall a. Ord a => (q, f a) -> Map a q


-- | This function constructs the product DDTA of the given two DDTAs.
prodDownState :: DownState f p -> DownState f q -> DownState f (p,q)
prodDownState sp sq ((p,q),t) = prodMap p q (sp (p, t)) (sq (q, t))


-- | This type is needed to construct the product of two DDTAs.
data ProdState p q = LState p
                   | RState q
                   | BState p q
-- | This function constructs the pointwise product of two maps each
-- with a default value.
prodMap :: (Ord a) => p -> q -> Map a p -> Map a q -> Map a (p,q)
prodMap p q mp mq = Map.map final $ Map.unionWith combine ps qs
    where ps = Map.map LState mp
          qs = Map.map RState mq
          combine (LState p) (RState q) = BState p q
          combine (RState q) (LState p) = BState p q
          combine _ _                   = error "unexpected merging"
          final (LState p) = (p, q)
          final (RState q) = (p, q)
          final (BState p q) = (p,q)

appMap :: (Zippable f) => (forall a . Ord a => f a -> Map a q)
                       -> q -> f b -> f (q,b)
appMap qmap q s = fmap qfun s'
    where s' = number s
          qfun k@(Numbered (_,a)) = (Map.findWithDefault q k (qmap s') ,a)

-- | This function constructs a DDTT from a given stateful term
-- homomorphism with the state propagated by the given DDTA.
toDownTrans :: Zippable f => DownState f q -> QHom q f g -> DownTrans q f g
toDownTrans st f (q, s) = explicit q fst f (appMap (curry st q) q s)


-- | This function applies a given stateful term homomorphism with a
-- state space propagated by the given DDTA to a term.
downHom :: (Zippable f, Functor g)
            => DownState f q -> QHom q f g -> q -> Term f -> Term g
downHom st h = runDownTrans (toDownTrans st h)

-- | This type represents transition functions of generalised
-- deterministic top-down tree acceptors (GDDTAs) which have access
-- to an extended state space.
type GDownState f q p = forall a . (Ord a, ?below :: a -> p, ?above :: p, q :< p)
                                => f a -> Map a q

-- | This combinator turns an arbitrary DDTA into a GDDTA.
gDownState :: Functor f => DownState f q -> GDownState f q p
gDownState f t = f (above,t)

-- | This combinator turns a GDDTA with the smallest possible state
-- space into a DDTA.
downState :: GDownState f q q -> DownState f q
downState f (q,s) = res
    where res = explicit q bel f s
          bel k = Map.findWithDefault q k res


-- | This combinator constructs the product of two GDDTA.
prodGDownState :: (p :< pq, q :< pq, Functor f)
               => GDownState f p pq -> GDownState f q pq -> GDownState f (p,q) pq
prodGDownState sp sq t = prodMap above above (sp t) (sq t)

-- type GState f u d q = forall a . (Ord a, ?below :: a -> q, ?above :: q, u :< q, d :< q)
--                                => f a -> (u, Map a d)
runGState :: forall f d u . Zippable f => 
             GUpState f u (d,u) -> GDownState f d (d,u) -> d -> Term f -> u
runGState up down = run where
    run :: d -> Term f -> u
    run d (Term t) = u where
        t' :: f (Numbered (d,u))
        t' = fmap bel $ number t
        bel :: Numbered (Term f) -> Numbered (d,u)
        bel (Numbered (i,s)) = 
            let d' = Map.findWithDefault d (Numbered (i,undefined)) m
            in Numbered (i, (d', run d' s))
        m :: Map (Numbered (d,u)) d
        m = explicit (d,u) unNumbered down t'
        u :: u
        u = explicit (d,u) unNumbered up t'
        
    
-------------
-- Example --
-------------

data Str a = Str
data Base a = Char | List a

type Typ = Str :+: Base

$(derive [makeFunctor,smartConstructors, makeShowF] [''Str,''Base])

class StringType f g where
    strTypeHom :: (Bool :< q) => QHom q f g

$(derive [liftSum] [''StringType])

strType :: (Base :<: f, Functor f, Functor g, StringType f g)
        => Term f -> Term g
strType = snd . upHom isCharAlg strTypeHom

isCharAlg :: (Base :<: f) => Alg f Bool
isCharAlg t = case proj t of
                Just Char -> True
                _ -> False
    
instance (Str :<: f, Functor f) =>  StringType Str f where
    strTypeHom = simpCxt . inj

instance (Str :<:  f, Base :<: f, Functor f) =>  StringType Base f where
    strTypeHom Char = iChar
    strTypeHom (List t)
               | below t  = iStr 
               | otherwise = iList $ Hole t


ex1 :: Term Typ
ex1 = iList iChar

runEx1 :: Term Typ
runEx1 = strType ex1