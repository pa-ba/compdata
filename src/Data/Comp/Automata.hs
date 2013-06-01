{-# LANGUAGE Rank2Types, FlexibleContexts, ImplicitParams, GADTs, TypeOperators #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Automata
-- Copyright   :  (c) 2010-2012 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines stateful term homomorphisms. This (slightly
-- oxymoronic) notion extends per se stateless term homomorphisms with
-- a state that is maintained separately by a bottom-up or top-down
-- state transformation. Additionally, this module also provides
-- combinators to run state transformations themselves.
-- 
-- Like regular term homomorphisms also stateful homomorphisms (as
-- well as transducers) can be lifted to annotated signatures
-- (cf. "Data.Comp.Annotation").
--
-- The recursion schemes provided in this module are derived from tree
-- automata. They allow for a higher degree of modularity and make it
-- possible to apply fusion. The implementation is based on the paper
-- /Modular Tree Automata/ (Mathematics of Program Construction,
-- 263-299, 2012, <http://dx.doi.org/10.1007/978-3-642-31113-0_14>).
--
--------------------------------------------------------------------------------

module Data.Comp.Automata
    (
    -- * Stateful Term Homomorphisms
      QHom
    , below
    , above
    , pureHom
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
    , UpTrans'
    , mkUpTrans
    , runUpTrans
    , compUpTrans
    , compUpTransHom
    , compHomUpTrans
    , compUpTransSig
    , compSigUpTrans
    , compAlgUpTrans
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
    , DownTrans'
    , mkDownTrans
    , runDownTrans
    , compDownTrans
    , compDownTransSig
    , compSigDownTrans
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
    -- * Product State Spaces
    , module Data.Comp.Automata.Product
    ) where

import Data.Comp.Number
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

explicit :: ((?above :: q, ?below :: a -> q) => b) -> q -> (a -> q) -> b
explicit x ab be = x where ?above = ab; ?below = be


-- | This type represents stateful term homomorphisms. Stateful term
-- homomorphisms have access to a state that is provided (separately)
-- by a bottom-up or top-down state transformation function (or both).
                           
type QHom f q g = forall a . (?below :: a -> q, ?above :: q) => f a -> Context g a


-- | This function turns a stateful homomorphism with a fully
-- polymorphic state type into a (stateless) homomorphism.
pureHom :: (forall q . QHom f q g) -> Hom f g
pureHom phom t = let ?above = undefined 
                     ?below = const undefined
                 in phom t

-- | This type represents transition functions of total, deterministic
-- bottom-up tree transducers (UTTs).

type UpTrans f q g = forall a. f (q,a) -> (q, Context g a)


-- | This is a variant of the 'UpTrans' type that makes it easier to
-- define UTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type UpTrans' f q g = forall a. f (q,Context g a) -> (q, Context g a)

-- | This function turns a UTT defined using the type 'UpTrans'' in
-- to the canonical form of type 'UpTrans'.

mkUpTrans :: Functor f => UpTrans' f q g -> UpTrans f q g
mkUpTrans tr t = tr $ fmap (\(q,a) -> (q, Hole a)) t

-- | This function transforms a UTT transition function into an
-- algebra.

upAlg :: (Functor g)  => UpTrans f q g -> Alg f (q, Term g)
upAlg trans = fmap appCxt . trans 

-- | This function runs the given UTT on the given term.

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

-- | This function composes two UTTs. (see TATA, Theorem 6.4.5)
    
compUpTrans :: (Functor f, Functor g, Functor h)
               => UpTrans g p h -> UpTrans f q g -> UpTrans f (q,p) h
compUpTrans t2 t1 x = ((q1,q2), c2) where
    (q1, c1) = t1 $ fmap (\((q1,q2),a) -> (q1,(q2,a))) x
    (q2, c2) = runUpTrans' t2 c1


-- | This function composes a UTT with an algebra.
    
compAlgUpTrans :: (Functor g)
               => Alg g a -> UpTrans f q g -> Alg f (q,a)
compAlgUpTrans alg trans = fmap (cata' alg) . trans


-- | This combinator composes a UTT followed by a signature function.

compSigUpTrans :: (Functor g) => SigFun g h -> UpTrans f q g -> UpTrans f q h
compSigUpTrans sig trans x = (q, appSigFun sig x') where
    (q, x') = trans x

-- | This combinator composes a signature function followed by a UTT.
    
compUpTransSig :: UpTrans g q h -> SigFun f g -> UpTrans f q h
compUpTransSig trans sig = trans . sig

-- | This combinator composes a UTT followed by a homomorphism.

compHomUpTrans :: (Functor g, Functor h) => Hom g h -> UpTrans f q g -> UpTrans f q h
compHomUpTrans hom trans x = (q, appHom hom x') where
    (q, x') = trans x

-- | This combinator composes a homomorphism followed by a UTT.
    
compUpTransHom :: (Functor g, Functor h) => UpTrans g q h -> Hom f g -> UpTrans f q h
compUpTransHom trans hom x  = runUpTrans' trans . hom $ x

-- | This type represents transition functions of total, deterministic
-- bottom-up tree acceptors (UTAs).

type UpState f q = Alg f q

-- | Changes the state space of the UTA using the given isomorphism.

tagUpState :: (Functor f) => (q -> p) -> (p -> q) -> UpState f q -> UpState f p
tagUpState i o s = i . s . fmap o

-- | This combinator runs the given UTA on a term returning the final
-- state of the run.

runUpState :: (Functor f) => UpState f q -> Term f -> q
runUpState = cata

-- | This function combines the product UTA of the two given UTAs.

prodUpState :: Functor f => UpState f p -> UpState f q -> UpState f (p,q)
prodUpState sp sq t = (p,q) where
    p = sp $ fmap fst t
    q = sq $ fmap snd t


-- | This function constructs a UTT from a given stateful term
-- homomorphism with the state propagated by the given UTA.
    
upTrans :: (Functor f, Functor g) => UpState f q -> QHom f q g -> UpTrans f q g
upTrans st f t = (q, c)
    where q = st $ fmap fst t
          c = fmap snd $ explicit f q fst t

-- | This function applies a given stateful term homomorphism with
-- a state space propagated by the given UTA to a term.
          
runUpHom :: (Functor f, Functor g) => UpState f q -> QHom f q g -> Term f -> Term g
runUpHom st hom = snd . runUpHomSt st hom

-- | This is a variant of 'runUpHom' that also returns the final state
-- of the run.

runUpHomSt :: (Functor f, Functor g) => UpState f q -> QHom f q g -> Term f -> (q,Term g)
runUpHomSt alg h = runUpTransSt (upTrans alg h)


-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GUTAs) which have access
-- to an extended state space.

type DUpState f p q = forall a . (?below :: a -> p, ?above :: p, q :< p) => f a -> q

-- | This combinator turns an arbitrary UTA into a GUTA.

dUpState :: Functor f => UpState f q -> DUpState f p q
dUpState f = f . fmap below

-- | This combinator turns a GUTA with the smallest possible state
-- space into a UTA.

upState :: DUpState f q q -> UpState f q
upState f s = res where res = explicit f res id s

-- | This combinator runs a GUTA on a term.
                        
runDUpState :: Functor f => DUpState f q q -> Term f -> q
runDUpState = runUpState . upState

-- | This combinator constructs the product of two GUTA.

prodDUpState :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
prodDUpState sp sq t = (sp t, sq t)

(<*>) :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p,q)
(<*>) = prodDUpState



-- | This type represents transition functions of total deterministic
-- top-down tree transducers (DTTs).

type DownTrans f q g = forall a. q -> f (q -> a) -> Context g a


-- | This is a variant of the 'DownTrans' type that makes it easier to
-- define DTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type DownTrans' f q g = forall a. q -> f (q -> Context g a) -> Context g a

-- | This function turns a DTT defined using the type 'DownTrans'' in
-- to the canonical form of type 'DownTrans'.
mkDownTrans :: Functor f => DownTrans' f q g -> DownTrans f q g
mkDownTrans tr q t = tr q (fmap (Hole .) t)

-- | Thsis function runs the given DTT on the given tree.

runDownTrans :: (Functor f, Functor g) => DownTrans f q g -> q -> Cxt h f a -> Cxt h g a
runDownTrans tr q t = run t q where
    run (Term t) q = appCxt $ tr q $ fmap run t
    run (Hole a) _ = Hole a

-- | This function runs the given DTT on the given tree.
    
runDownTrans' :: (Functor f, Functor g) => DownTrans f q g -> q -> Cxt h f (q -> a) -> Cxt h g a
runDownTrans' tr q t = run t q where
    run (Term t) q = appCxt $ tr q $ fmap run $ t
    run (Hole a) q = Hole (a q)

-- | This function composes two DTTs. (see W.C. Rounds /Mappings and
-- grammars on trees/, Theorem 2.)
    
compDownTrans :: (Functor f, Functor g, Functor h)
              => DownTrans g p h -> DownTrans f q g -> DownTrans f (q,p) h
compDownTrans t2 t1 (q,p) t = runDownTrans' t2  p $ t1 q (fmap curry t)



-- | This function composes a signature function after a DTT.

compSigDownTrans :: (Functor g) => SigFun g h -> DownTrans f q g -> DownTrans f q h
compSigDownTrans sig trans q = appSigFun sig . trans q

-- | This function composes a DTT after a function.

compDownTransSig :: DownTrans g q h -> SigFun f g -> DownTrans f q h
compDownTransSig trans hom q t = trans q (hom t)


-- | This function composes a homomorphism after a DTT.

compHomDownTrans :: (Functor g, Functor h)
              => Hom g h -> DownTrans f q g -> DownTrans f q h
compHomDownTrans hom trans q = appHom hom . trans q

-- | This function composes a DTT after a homomorphism.

compDownTransHom :: (Functor g, Functor h)
              => DownTrans g q h -> Hom f g -> DownTrans f q h
compDownTransHom trans hom q t = runDownTrans' trans q (hom t)


-- | This type represents transition functions of total, deterministic
-- top-down tree acceptors (DTAs).

type DownState f q = forall a. Ord a => (q, f a) -> Map a q


-- | Changes the state space of the DTA using the given isomorphism.

tagDownState :: (q -> p) -> (p -> q) -> DownState f q -> DownState f p
tagDownState i o t (q,s) = fmap i $ t (o q,s)

-- | This function constructs the product DTA of the given two DTAs.

prodDownState :: DownState f p -> DownState f q -> DownState f (p,q)
prodDownState sp sq ((p,q),t) = prodMap p q (sp (p, t)) (sq (q, t))


-- | This type is needed to construct the product of two DTAs.

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
          
appMap :: Traversable f => (forall i . Ord i => f i -> Map i q)
                       -> q -> f (q -> b) -> f (q,b)
appMap qmap q s = fmap qfun s'
    where s' = number s
          qfun k@(Numbered (_,a)) = let q' = Map.findWithDefault q k (qmap s')
                                    in (q', a q') 

-- | This function constructs a DTT from a given stateful term--
-- homomorphism with the state propagated by the given DTA.
          
downTrans :: (Traversable f, Functor g) => DownState f q -> QHom f q g -> DownTrans f q g
downTrans st f q s = fmap snd $ explicit f q fst (appMap (curry st q) q s)


-- | This function applies a given stateful term homomorphism with a
-- state space propagated by the given DTA to a term.

runDownHom :: (Traversable f, Functor g)
            => DownState f q -> QHom f q g -> q -> Term f -> Term g
runDownHom st h = runDownTrans (downTrans st h)

-- | This type represents transition functions of generalised
-- deterministic top-down tree acceptors (GDTAs) which have access

-- to an extended state space.
type DDownState f p q = forall i . (Ord i, ?below :: i -> p, ?above :: p, q :< p)
                                => f i -> Map i q

-- | This combinator turns an arbitrary DTA into a GDTA.

dDownState :: DownState f q -> DDownState f p q
dDownState f t = f (above,t)

-- | This combinator turns a GDTA with the smallest possible state
-- space into a DTA.

downState :: DDownState f q q -> DownState f q
downState f (q,s) = res
    where res = explicit f q bel s
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

runDState :: Traversable f => DUpState f (u,d) u -> DDownState f (u,d) d -> d -> Term f -> u
runDState up down d (Term t) = u where
        t' = fmap bel $ number t
        bel (Numbered (i,s)) = 
            let d' = Map.findWithDefault d (Numbered (i,undefined)) m
            in Numbered (i, (runDState up down d' s, d'))
        m = explicit down (u,d) unNumbered t'
        u = explicit up (u,d) unNumbered t'

-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.
        
runQHom :: (Traversable f, Functor g) =>
           DUpState f (u,d) u -> DDownState f (u,d) d -> 
           QHom f (u,d) g ->
           d -> Term f -> (u, Term g)
runQHom up down trans d (Term t) = (u,t'') where
        t' = fmap bel $ number t
        bel (Numbered (i,s)) = 
            let d' = Map.findWithDefault d (Numbered (i,undefined)) m
                (u', s') = runQHom up down trans d' s
            in Numbered (i, ((u', d'),s'))
        m = explicit down (u,d) (fst . unNumbered) t'
        u = explicit up (u,d) (fst . unNumbered) t'
        t'' = appCxt $ fmap (snd . unNumbered) $  explicit trans (u,d) (fst . unNumbered) t'