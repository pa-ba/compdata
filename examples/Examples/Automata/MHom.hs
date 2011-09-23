{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, TypeOperators,
  ImplicitParams, GADTs, IncoherentInstances, ScopedTypeVariables,
  TupleSections #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MHom
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Examples.Automata.MHom
    ( module Examples.Automata.MHom
    , module Data.Stream ) where

import Data.Comp.Zippable
import Data.Comp
import Data.Comp.Ops
import Data.Stream (Stream(..), (<:>))
import Data.Comp.Show ()
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad
import Control.Arrow (first, (&&&))
import Data.Comp.Derive

-- | An instance @a :< b@ means that @a@ is a component of @b@. @a@
-- can be extracted from @b@ via the method 'ex'.
class p :< q where
    pr :: q a -> p a
    up :: p a -> q a -> q a

instance q :< q where
    pr = id
    up = const

instance p :< p :*: q where
    pr = ffst
    up x (_ :*: y) = x :*: y

instance (p :< q) => p :< (p' :*: q) where
    pr = pr . fsnd
    up  y (x :*: y') = x :*: up y y'

-- | This function provides access to components of the states from
-- "below".
below :: (?below :: i -> q a, p :< q) => i -> p a
below = pr . ?below

-- | This function provides access to components of the state from
-- "above"
above :: (?above :: q a, p :< q) => p a
above = pr ?above

hole :: (?get :: i -> a) => i -> Context f a
hole = Hole . ?get

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.
explicit :: q a -> (i -> q a) -> (i -> a)
         -> ((?get :: i -> a, ?below :: i -> q a, ?above :: q a) => b) -> b
explicit ab bel get x = x
    where ?above = ab
          ?below = bel
          ?get = get
-- | This type represents generalised term homomorphisms. Generalised
-- term homomorphisms have access to a state that is provided
-- (separately) by a DUTA or a DDTA (or both).
type MHom q f g = forall a i . (?get :: i -> a, ?below :: i -> q a, ?above :: q a)
    => f i -> Context g a


-- | This type represents transition functions of deterministic
-- bottom-up tree transducers (DUTTs).

type UpTrans q f g = forall a. f (q a,a) -> (q (Context g a), Context g a)

-- | This function transforms DUTT transition function into an
-- algebra.
upAlg :: (Functor g, Functor q)  => UpTrans q f g -> Alg f (q (Term g), Term g)
upAlg trans t = let (q , c) = trans t
                in (fmap appCxt q, appCxt c)


-- | This function runs the given DUTT on the given term.

runUpTrans :: (Functor f, Functor g, Functor q) => UpTrans q f g -> Term f -> (q (Term g), Term g)
runUpTrans = cata . upAlg

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.
runUpTrans' :: (Functor f, Functor g, Functor q)
            => UpTrans q f g -> Context f (q a,a) -> (q (Context g a), Context g a)
runUpTrans' trans = run where
    run (Hole (q,a)) = (fmap Hole q, Hole a)
    run (Term t) = let (q, c) = trans $ fmap run t
                   in (fmap appCxt q, appCxt c)

-- | This function composes two DUTTs. (I'm not sure whether it is correct, yet.)
compUpTrans :: (Functor f, Functor g, Functor h, Functor q1, Functor q2)
               => UpTrans q2 g h -> UpTrans q1 f g -> UpTrans (q1 :*: q2) f h
compUpTrans t2 t1 x = (q1' :*: q2, c2) where
    (q1, c1) = t1 $ fmap shuffle  x
    shuffle (q1 :*: q2,a) = (fmap (q2,) q1 ,(q2,a) )
    q1' = fmap (snd . runUpTrans' t2) q1
    (q2, c2) = runUpTrans' t2 c1

-- | This type represents transition functions of deterministic
-- bottom-up tree acceptors (DUTAs).
type UpState f q = forall a . f (q a, a) -> q a

-- | This combinator runs the given DUTA on a term returning the final
-- state of the run.
runUpState :: (Functor f) => UpState f q -> Term f -> q (Term f)
runUpState st = run where
    run (Term t) = st $ fmap (\ s -> (run s, s)) t


-- | This function combines the product DUTA of the two given DUTAs.
prodUpState :: Functor f => UpState f p -> UpState f q -> UpState f (p :*:q)
prodUpState sp sq t = p :*: q where
    p = sp $ fmap (first ffst) t
    q = sq $ fmap (first fsnd) t

-- | This function turns constructs a DUTT from a given macro term
-- homomorphism with the state propagated by the given DUTA.
toUpTrans :: (Functor f, Functor g, Functor q)
          => UpState f q -> MHom q f g -> UpTrans q f g
toUpTrans st f t = (fmap Hole q, c)
    where q = st t
          c = explicit q (pr . fst) snd f t

-- | This function applies a given generalised term homomorphism with
-- a state space propagated by the given DUTA to a term.
upHom :: (Functor f, Functor g, Functor q) => UpState f q -> MHom q f g -> Term f -> (q (Term g),Term g)
upHom alg h = runUpTrans (toUpTrans alg h)

-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GDUTAs) which have access
-- to an extended state space.
type GUpState f q p = forall a i . (?get :: i -> a, ?below :: i -> p a, ?above :: p a, q :< p) => f i -> q a

-- | This combinator turns an arbitrary DUTA into a GDUTA.
gUpState :: Functor f => UpState f q -> GUpState f q p
gUpState f = f . fmap (below &&& (?get))

-- | This combinator turns a GDUTA with the smallest possible state
-- space into a DUTA.
upState :: GUpState f q q -> UpState f q
upState f s = let res = explicit res fst snd f s in res

-- | This combinator runs a GDUTA on a term.
runGUpState :: Functor f => GUpState f q q -> Term f -> q (Term f)
runGUpState s = runUpState (upState s)

-- | This combinator constructs the product of two GDUTA.
prodGUpState :: (p :< pq, q :< pq)
             => GUpState f p pq -> GUpState f q pq -> GUpState f (p :*: q) pq
prodGUpState sp sq t = sp t :*: sq t

-- | This type represents transition functions of deterministic
-- top-down tree transducers (DDTTs).

type DownTrans q f g = forall a. (q a, f a) -> Context g (q (Context f a),a)

-- | This function runs the given DDTT on the given tree.
runDownTrans :: (Functor f, Functor g, Functor q) => DownTrans q f g -> q (Cxt h g a) -> Cxt h f a -> Cxt h g a
runDownTrans tr q t = run (q,t) where
    run (q,Term t) = appCxt $ fmap (\(q,a) -> run (fmap appCxt q,a)) $  tr (q, t)
    run (_,Hole a) = Hole a

-- | This function runs the given DDTT on the given tree.
runDownTrans' :: (Functor f, Functor g, Functor q) => DownTrans q f g -> q (Cxt h f a)
              -> Cxt h f a -> Cxt h g (q (Cxt h f a),a)
runDownTrans' tr q t = run (q,t) where
    run (q,Term t) = appCxt $ fmap (\(q,a) -> run (fmap appCxt q,a)) $  tr (q, t)
    run (q,Hole a)      = Hole (q,a)

-- | This function composes two DDTTs. (not implemented yet)
compDownTrans :: (Functor f, Functor g, Functor h)
              => DownTrans p g h -> DownTrans q f g -> DownTrans (q :*:p) f h
compDownTrans = undefined

-- | This type represents transition functions of deterministic
-- top-down tree acceptors (DDTAs).
type DownState f q = forall a i. Ord i => (q a, f (i,a)) -> Map i (q a)

-- | This function constructs the product DDTA of the given two DDTAs.
prodDownState :: DownState f p -> DownState f q -> DownState f (p :*: q)
prodDownState sp sq (p :*: q,t) = prodMap p q (sp (p, t)) (sq (q, t))



-- | This type is needed to construct the product of two DDTAs.
data ProdState p q = LState p
                   | RState q
                   | BState p q
-- | This function constructs the pointwise product of two maps each
-- with a default value.
prodMap :: (Ord i) => p a -> q a -> Map i (p a) -> Map i (q a) -> Map i ((p :*: q) a)
prodMap p q mp mq = Map.map final $ Map.unionWith combine ps qs
    where ps = Map.map LState mp
          qs = Map.map RState mq
          combine (LState p) (RState q) = BState p q
          combine (RState q) (LState p) = BState p q
          combine _ _                   = error "unexpected merging"
          final (LState p) = p :*: q
          final (RState q) = p :*: q
          final (BState p q) = p :*: q

-- | Apply the given state mapping to the given functorial value by
-- adding the state to the corresponding index if it is in the map and
-- otherwise adding the provided default state.
appMap :: Zippable f => DownState f q -> q a -> f a -> f (q a,a)
appMap qmap q s = fmap qfun s'
    where s' = number' s
          mapping  = qmap (q,s')
          qfun (k,a) = (Map.findWithDefault q k mapping ,a)

-- -- | This function constructs a DDTT from a given stateful term
-- -- homomorphism with the state propagated by the given DDTA.
-- toDownTrans :: (Zippable f, Functor q) => DownState f q -> MHom q f g -> DownTrans q f g
-- toDownTrans st f (q, s) = fmap mkQCxt $ explicit q fst id f (appMap st q s)
--     where mkQCxt (q,a) = (fmap Hole q, a)