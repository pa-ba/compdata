{-# LANGUAGE RankNTypes, FlexibleContexts, ImplicitParams, GADTs, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Automata
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

module Data.Comp.Automata
    ( module Data.Comp.Automata.Product
    -- * Stateful Term Homomorphisms
    , QHom
    , below
    , above
    -- ** Bottom-Up State Propagation
    , upTrans
    , runUpHom
    , runUpHomSt
    -- ** Top-Down State Propagation
    , downTrans
    , runDownHom
    -- ** Bidirectional State Propagation
    , runQHom
    -- * Deterministic Bottom-Up Tree Transducers
    , UpTrans
    , runUpTrans
    , compUpTrans
    , compUpTransHom
    , compHomUpTrans
    -- * Deterministic Bottom-Up Tree State Transformations
    -- ** Monolithic State
    , UpState
    , tagUpState
    , runUpState
    , prodUpState
    -- ** Modular State
    , DUpState
    , dUpState
    , upState
    , runDUpState
    , prodDUpState
    , (<*>)
    -- * Deterministic Top-Down Tree Transducers
    , DownTrans
    , runDownTrans
    , compDownTrans
    , compDownTransHom
    , compHomDownTrans
    -- * Deterministic Top-Down Tree State Transformations
    -- ** Monolithic State
    , DownState
    , tagDownState
    , prodDownState
    -- ** Modular State
    , DDownState
    , dDownState
    , downState
    , prodDDownState
    , (>*<)
    -- * Bidirectional Tree State Transformations
    , runDState
    -- * Operators for Finite Mappings
    , (&)
    , (|->)
    , o
    ) where

import Data.Comp.Zippable
import Data.Comp.Automata.Product
import Data.Comp.Term
import Data.Comp.Algebra
import Data.Map (Map)
import qualified Data.Map as Map


-- The following are operators to specify finite mappings.


infix 1 |->
infixr 0 &

-- | left-biased union of two mappings.
(&) :: Ord k => Map k v -> Map k v -> Map k v
(&) = Map.union

-- | This operator constructs a singleton mapping.
(|->) :: k -> a -> Map k a
(|->) = Map.singleton

-- | This is the empty mapping.
o :: Map k a
o = Map.empty

-- | This function provides access to components of the states from
-- "below".
below :: (?below :: a -> q, p :< q) => a -> p
below = pr . ?below

-- | This function provides access to components of the state from
-- "above"
above :: (?above :: q, p :< q) => p
above = pr ?above

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.
explicit :: q -> (a -> q) -> ((?above :: q, ?below :: a -> q) => b) -> b
explicit ab be x = x where ?above = ab; ?below = be


-- | This type represents stateful term homomorphisms. Stateful term
-- homomorphisms have access to a state that is provided (separately)
-- by a DUTA or a DDTA (or both).
type QHom f q g = forall a . (?below :: a -> q, ?above :: q) => f a -> Context g a

-- -- | This type represents (pure, i.e. stateless) homomorphism by
-- -- universally quantifying over the state type.
-- type PHom f g = forall q . QHom f q g

-- -- | This combinator runs a stateless homomorphism. (use
-- -- 'Data.Comp.Algebra.appHom' instead).
-- runPHom :: forall f g . (Functor f, Functor g) => PHom f g -> CxtFun f g
-- runPHom hom = run where
--     run :: CxtFun f g
--     run (Hole x) = Hole x
--     run (Term t) = appCxt (explicit () (const ()) hom (fmap run t))

-- | This type represents transition functions of deterministic
-- bottom-up tree transducers (DUTTs).

type UpTrans f q g = forall a. f (q,a) -> (q, Context g a)

-- | This function transforms DUTT transition function into an
-- algebra.

upAlg :: (Functor g)  => UpTrans f q g -> Alg f (q, Term g)
upAlg trans = fmap appCxt . trans 

-- | This function runs the given DUTT on the given term.

runUpTrans :: (Functor f, Functor g) => UpTrans f q g -> Term f -> Term g
runUpTrans trans = snd . runUpTransSt trans

-- | This function is a variant of 'runUpTrans' that additionally
-- returns the final state of the run.

runUpTransSt :: (Functor f, Functor g) => UpTrans f q g -> Term f -> (q, Term g)
runUpTransSt = cata . upAlg

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.
runUpTrans' :: (Functor f, Functor g) => UpTrans f q g -> Context f (q,a) -> (q, Context g a)
runUpTrans' trans = run where
    run (Hole (q,a)) = (q, Hole a)
    run (Term t) = fmap appCxt $ trans $ fmap run t

-- | This function composes two DUTTs. (see TATA, Theorem 6.4.5)
compUpTrans :: (Functor f, Functor g, Functor h)
               => UpTrans g p h -> UpTrans f q g -> UpTrans f (q,p) h
compUpTrans t2 t1 x = ((q1,q2), c2) where
    (q1, c1) = t1 $ fmap (\((q1,q2),a) -> (q1,(q2,a))) x
    (q2, c2) = runUpTrans' t2 c1


-- | This combinator composes a DUTT followed by a homomorphism.
compHomUpTrans :: (Functor g, Functor h) => Hom g h -> UpTrans f q g -> UpTrans f q h
compHomUpTrans hom trans x = (q, appHom hom x') where
    (q, x') = trans x

-- | This combinator composes a homomorphism followed by a DUTT.
compUpTransHom :: (Functor g, Functor h) => UpTrans g q h -> Hom f g -> UpTrans f q h
compUpTransHom trans hom x  = runUpTrans' trans . hom $ x

-- | This type represents transition functions of deterministic
-- bottom-up tree acceptors (DUTAs).
type UpState f q = Alg f q

-- | Changes the state space of the DUTA using the given isomorphism.
tagUpState :: (Functor f) => (q -> p) -> (p -> q) -> UpState f q -> UpState f p
tagUpState i o s = i . s . fmap o

-- | This combinator runs the given DUTA on a term returning the final
-- state of the run.
runUpState :: (Functor f) => UpState f q -> Term f -> q
runUpState = cata

-- | This function combines the product DUTA of the two given DUTAs.
prodUpState :: Functor f => UpState f p -> UpState f q -> UpState f (p,q)
prodUpState sp sq t = (p,q) where
    p = sp $ fmap fst t
    q = sq $ fmap snd t


-- | This function constructs a DUTT from a given stateful term
-- homomorphism with the state propagated by the given DUTA.
upTrans :: (Functor f, Functor g) => UpState f q -> QHom f q g -> UpTrans f q g
upTrans st f t = (q, c)
    where q = st $ fmap fst t
          c = fmap snd $ explicit q fst f t

-- | This function applies a given stateful term homomorphism with
-- a state space propagated by the given DUTA to a term.
runUpHom :: (Functor f, Functor g) => UpState f q -> QHom f q g -> Term f -> Term g
runUpHom st hom = snd . runUpHomSt st hom

-- | This is a variant of 'runUpHom' that also returns the final state
-- of the run.
runUpHomSt :: (Functor f, Functor g) => UpState f q -> QHom f q g -> Term f -> (q,Term g)
runUpHomSt alg h = runUpTransSt (upTrans alg h)


-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GDUTAs) which have access
-- to an extended state space.
type DUpState f p q = forall a . (?below :: a -> p, ?above :: p, q :< p) => f a -> q

-- | This combinator turns an arbitrary DUTA into a GDUTA.
dUpState :: Functor f => UpState f q -> DUpState f p q
dUpState f = f . fmap below

-- | This combinator turns a GDUTA with the smallest possible state
-- space into a DUTA.
upState :: DUpState f q q -> UpState f q
upState f s = res where res = explicit res id f s

-- | This combinator runs a GDUTA on a term.
runDUpState :: Functor f => DUpState f q q -> Term f -> q
runDUpState = runUpState . upState

-- | This combinator constructs the product of two GDUTA.
prodDUpState :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
prodDUpState sp sq t = (sp t, sq t)

(<*>) :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
(<*>) = prodDUpState



-- | This type represents transition functions of deterministic
-- top-down tree transducers (DDTTs).

type DownTrans f q g = forall a. (q, f a) -> Context g (q,a)

-- | Thsis function runs the given DDTT on the given tree.
runDownTrans :: (Functor f, Functor g) => DownTrans f q g -> q -> Cxt h f a -> Cxt h g a
runDownTrans tr q t = run (q,t) where
    run (q,Term t) = appCxt $ fmap run $  tr (q, t)
    run (_,Hole a)      = Hole a

-- | This function runs the given DDTT on the given tree.
runDownTrans' :: (Functor f, Functor g) => DownTrans f q g -> q -> Cxt h f a -> Cxt h g (q,a)
runDownTrans' tr q t = run (q,t) where
    run (q,Term t) = appCxt $ fmap run $  tr (q, t)
    run (q,Hole a)      = Hole (q,a)

-- | This function composes two DDTTs. (see Z. Fülöp, H. Vogler
-- "Syntax-Directed Semantics", Theorem 3.39)
compDownTrans :: (Functor f, Functor g, Functor h)
              => DownTrans g p h -> DownTrans f q g -> DownTrans f (q,p) h
compDownTrans t2 t1 ((q,p), t) = fmap (\(p, (q, a)) -> ((q,p),a)) $ runDownTrans' t2 p (t1 (q, t))


-- | This function composes a homomorphism after a DDTT.
compHomDownTrans :: (Functor g, Functor h)
              => Hom g h -> DownTrans f q g -> DownTrans f q h
compHomDownTrans hom trans = appHom hom . trans

-- | This function composes a DDTT after a homomorphism.
compDownTransHom :: (Functor g, Functor h)
              => DownTrans g q h -> Hom f g -> DownTrans f q h
compDownTransHom trans hom (q,t) = runDownTrans' trans q (hom t)


-- | This type represents transition functions of deterministic
-- top-down tree acceptors (DDTAs).
type DownState f q = forall a. Ord a => (q, f a) -> Map a q


-- | Changes the state space of the DDTA using the given isomorphism.
tagDownState :: (q -> p) -> (p -> q) -> DownState f q -> DownState f p
tagDownState i o t (q,s) = fmap i $ t (o q,s)

-- | This function constructs the product DDTA of the given two DDTAs.
prodDownState :: DownState f p -> DownState f q -> DownState f (p,q)
prodDownState sp sq ((p,q),t) = prodMap p q (sp (p, t)) (sq (q, t))


-- | This type is needed to construct the product of two DDTAs.
data ProdState p q = LState p
                   | RState q
                   | BState p q
-- | This function constructs the pointwise product of two maps each
-- with a default value.
prodMap :: (Ord i) => p -> q -> Map i p -> Map i q -> Map i (p,q)
prodMap p q mp mq = Map.map final $ Map.unionWith combine ps qs
    where ps = Map.map LState mp
          qs = Map.map RState mq
          combine (LState p) (RState q) = BState p q
          combine (RState q) (LState p) = BState p q
          combine _ _                   = error "unexpected merging"
          final (LState p) = (p, q)
          final (RState q) = (p, q)
          final (BState p q) = (p,q)

-- | Apply the given state mapping to the given functorial value by
-- adding the state to the corresponding index if it is in the map and
-- otherwise adding the provided default state.
appMap :: Zippable f => (forall i . Ord i => f i -> Map i q)
                       -> q -> f b -> f (q,b)
appMap qmap q s = fmap qfun s'
    where s' = number s
          qfun k@(Numbered (_,a)) = (Map.findWithDefault q k (qmap s') ,a)

-- | This function constructs a DDTT from a given stateful term-- homomorphism with the state propagated by the given DDTA.
downTrans :: Zippable f => DownState f q -> QHom f q g -> DownTrans f q g
downTrans st f (q, s) = explicit q fst f (appMap (curry st q) q s)


-- | This function applies a given stateful term homomorphism with a
-- state space propagated by the given DDTA to a term.
runDownHom :: (Zippable f, Functor g)
            => DownState f q -> QHom f q g -> q -> Term f -> Term g
runDownHom st h = runDownTrans (downTrans st h)

-- | This type represents transition functions of generalised
-- deterministic top-down tree acceptors (GDDTAs) which have access
-- to an extended state space.
type DDownState f p q = forall i . (Ord i, ?below :: i -> p, ?above :: p, q :< p)
                                => f i -> Map i q

-- | This combinator turns an arbitrary DDTA into a GDDTA.
dDownState :: DownState f q -> DDownState f p q
dDownState f t = f (above,t)

-- | This combinator turns a GDDTA with the smallest possible state
-- space into a DDTA.
downState :: DDownState f q q -> DownState f q
downState f (q,s) = res
    where res = explicit q bel f s
          bel k = Map.findWithDefault q k res


-- | This combinator constructs the product of two dependant top-down
-- state transformations.
prodDDownState :: (p :< c, q :< c)
               => DDownState f c p -> DDownState f c q -> DDownState f c (p,q)
prodDDownState sp sq t = prodMap above above (sp t) (sq t)

-- | This is a synonym for 'prodDDownState'.
(>*<) :: (p :< c, q :< c, Functor f)
         => DDownState f c p -> DDownState f c q -> DDownState f c (p,q)
(>*<) = prodDDownState


-- | This combinator combines a bottom-up and a top-down state
-- transformations. Both state transformations can depend mutually
-- recursive on each other.
runDState :: Zippable f => DUpState f (u,d) u -> DDownState f (u,d) d -> d -> Term f -> u
runDState up down d (Term t) = u where
        t' = fmap bel $ number t
        bel (Numbered (i,s)) = 
            let d' = Map.findWithDefault d (Numbered (i,undefined)) m
            in Numbered (i, (runDState up down d' s, d'))
        m = explicit (u,d) unNumbered down t'
        u = explicit (u,d) unNumbered up t'

-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.
runQHom :: (Zippable f, Functor g) =>
           DUpState f (u,d) u -> DDownState f (u,d) d -> 
           QHom f (u,d) g ->
           d -> Term f -> (u, Term g)
runQHom up down trans d (Term t) = (u,t'') where
        t' = fmap bel $ number t
        bel (Numbered (i,s)) = 
            let d' = Map.findWithDefault d (Numbered (i,undefined)) m
                (u', s') = runQHom up down trans d' s
            in Numbered (i, ((u', d'),s'))
        m = explicit (u,d) (fst . unNumbered) down t'
        u = explicit (u,d) (fst . unNumbered) up t'
        t'' = appCxt $ fmap (snd . unNumbered) $  explicit (u,d) (fst . unNumbered) trans t'