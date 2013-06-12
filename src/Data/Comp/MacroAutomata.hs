{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MacroAutomata
-- Copyright   :  (c) 2013 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
-- 
-- This module defines macro tree transducers (MTTs). It provides
-- functions to run MTTs and to compose them with top down tree
-- transducers. It also defines MTTs with regular look-ahead which
-- combines MTTs with bottom-up tree acceptors.
--
--------------------------------------------------------------------------------

module Data.Comp.MacroAutomata
    (
     -- * Macro Tree Transducers
      MacroTrans
    , MacroTrans'
    , mkMacroTrans
    , runMacroTrans
    , compMacroDown
    , compDownMacro
    -- * Macro Tree Transducers with Singleton State Space
    , MacroTransId
    , MacroTransId'
    , fromMacroTransId
    , fromMacroTransId'
    -- * Macro Tree Transducers with Regular Look-Ahead
    , MacroTransLA
    , MacroTransLA'
    , mkMacroTransLA
    , runMacroTransLA
    -- * Macro Tree Transducers with Regular Look-Ahead
    , (:^:) (..)
    , I (..)
    )
    where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Automata
import Data.Comp.Ops
import Data.Comp.Multi.HFunctor (I (..))

-- | This type represents total deterministic macro tree transducers
-- (MTTs).

type MacroTrans f q g = forall a. q a -> f (q (Context g a) -> a) -> Context g a

-- | This is a variant of the type 'MacroTrans' that makes it easier
-- to define MTTs as it avoids the explicit use of 'Hole' when using
-- placeholders in the result.

type MacroTrans' f q g = forall a . q (Context g a) -> f (q (Context g a) -> Context g a)
                       -> Context g a

-- | This function turns an MTT defined using the more convenient type
-- 'MacroTrans'' into its canonical form of type 'MacroTrans'.

mkMacroTrans :: (Functor f, Functor q) => MacroTrans' f q g -> MacroTrans f q g
mkMacroTrans tr q t = tr (fmap Hole q) (fmap (Hole .) t)

-- | This function defines the semantics of MTTs. It applies a given
-- MTT to an input with and an initial state.

runMacroTrans :: (Functor g, Functor f, Functor q) => 
                 MacroTrans f q g -> q (Cxt h g a) -> Cxt h f a -> Cxt h g a
runMacroTrans tr q t = run t q where
    run (Term t) q = appCxt (tr q (fmap run' t))
    run (Hole a) _ = Hole a
    run' t q = run t (fmap appCxt q)
    

-- This function is a variant of 'runMacroTrans' that is used to
-- define composition. Restricted to 'Term's, both functions coincide.

runMacroTrans' :: forall g f q h a. 
                  (Functor g, Functor f, Functor q) => MacroTrans f q g -> q (Cxt h g a) 
               -> Cxt h f (q (Cxt h g a) -> a) -> Cxt h g a
runMacroTrans' tr q t = run t q where
    run :: Cxt h f (q (Cxt h g a) -> a) -> q (Cxt h g a) -> Cxt h g a
    run (Term t) q = appCxt (tr q (fmap run' t))
    run (Hole a) q = Hole (a q)

    run' :: Cxt h f (q (Cxt h g a) -> a) -> q (Context g (Cxt h g a)) -> Cxt h g a
    run' t q = run t (fmap appCxt q)


-- | This function composes a DTT followed by an MTT. The resulting
-- MTT's semantics is equivalent to the function composition of the
-- semantics of the original MTT and DTT.

compMacroDown :: (Functor f, Functor g, Functor h, Functor p)
              => MacroTrans g p h -> DownTrans f q g -> MacroTrans f (p :&: q) h
compMacroDown t2 t1 (p :&: q) t = runMacroTrans' t2 (fmap Hole p) (t1 q (fmap curryF t))
    where curryF :: ((p :&: q) a -> b) -> q -> p a -> b
          curryF f q p = f (p :&: q)

-- | This function is a variant of 'runDownTrans' that is used to
-- define composition, similarly to the function 'runMacroTrans''.

runDownTrans' :: (Functor f, Functor g) => DownTrans f q g -> q -> Cxt h f (q -> a) -> Cxt h g a
runDownTrans' tr q (Term t) = appCxt $ tr q $ fmap (\s q -> runDownTrans' tr q s) t
runDownTrans' _ q (Hole a) = Hole (a q)

-- | This type constructor is used to define the state space of an MTT
-- that is obtained by composing an MTT followed by a DTT.

data (q :^: p) a = q (p -> a) :^: p

instance Functor q => Functor (q :^: p) where
    fmap f (q :^: p) = fmap (f .) q :^: p

-- | This function composes an MTT followed by a DTT. The resulting
-- MTT's semantics is equivalent to first running the original MTT and
-- then the DTT.

compDownMacro :: forall f g h q p . (Functor f, Functor g, Functor h, Functor q)
              => DownTrans g p h -> MacroTrans f q g -> MacroTrans f (q :^: p) h
compDownMacro t2 t1 (q :^: p) t = runDownTrans' t2 p (t1 (fmap (\a p' -> a p') q) (fmap reshape t))
    where reshape :: ((q :^: p) (Context h a) -> a) -> (q (Context g (p -> a)) -> p -> a)
          reshape f q' p' = f (fmap (\s p'' -> runDownTrans' t2 p'' s) q' :^: p')


-- | This type is an instantiation of the 'MacroTrans' type to a state
-- space with only a single state with a single accumulation parameter
-- (i.e. the state space is the identity functor).

type MacroTransId  f g = forall a. a           -> f (Context g a -> a)           -> Context g a

-- | This type is a variant of the 'MacroTransId' which is more
-- convenient to work with as it avoids the explicit use of 'Hole' to
-- embed placeholders into the result.
type MacroTransId' f g = forall a. Context g a -> f (Context g a -> Context g a) -> Context g a


-- | This function transforms an MTT of type |MacroTransId| into the
-- canonical type such that it can be run.

fromMacroTransId :: Functor f => MacroTransId f g -> MacroTrans f I g
fromMacroTransId tr (I a) t = tr a (fmap (. I) t)


-- | This function transforms an MTT of type |MacroTransId'| into the
-- canonical type such that it can be run.

fromMacroTransId' :: Functor f => MacroTransId' f g -> MacroTrans f I g
fromMacroTransId' tr (I a) t = tr (Hole a) (fmap (\f -> Hole . f . I) t)

-- | This type represents MTTs with regular look-ahead, i.e. MTTs that
-- have access to information that is generated by a separate UTA.

type MacroTransLA  f q p g = forall a. q a -> p -> f (q (Context g a) -> a, p) -> Context g a

-- | This type is a more convenient variant of 'MacroTransLA' with
-- which one can avoid using 'Hole' explicitly when injecting
-- placeholders in the result.
type MacroTransLA' f q p g = forall a. q (Context g a) -> p -> 
                             f (q (Context g a) -> Context g a, p) -> Context g a


-- | This function turns an MTT with regular look-ahead defined using
-- the more convenient type |MacroTransLA'| into its canonical form of
-- type |MacroTransLA|.
mkMacroTransLA :: (Functor q, Functor f) => MacroTransLA' f q p g -> MacroTransLA f q p g
mkMacroTransLA tr q p t = tr (fmap Hole q) p (fmap (\ (f, p) -> (Hole . f,p)) t)


-- | This function defines the semantics of MTTs with regular
-- look-ahead. It applies a given MTT with regular look-ahead
-- (including an accompanying bottom-up state transition function) to
-- an input with and an initial state.
runMacroTransLA :: forall g f q p. (Functor g, Functor f, Functor q) => 
                   UpState f p -> MacroTransLA f q p g -> q (Term g) -> Term f -> Term g
runMacroTransLA st tr q t = fst (run t) q where
    run :: Term f -> (q (Term g) -> Term g, p)
    run (Term t) = let p = st $ fmap snd t'
                       t' = fmap run' t
                   in (\ q -> appCxt (tr q p t'), p)
    run' :: Term f -> (q (Context g (Term g)) -> (Term g), p)
    run' t = let (res, p) = run t
             in  (res . fmap appCxt, p)
