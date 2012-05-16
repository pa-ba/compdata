{-# LANGUAGE Rank2Types, FlexibleContexts, ImplicitParams, GADTs, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MacroAutomata
-- Copyright   :  (c) 2012 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.MacroAutomata where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Ops

type UpTrans f q g = forall a. f (q a, a) -> (q a, Context g a)

type GUpTrans f q g = forall a. f (q a, a) -> (q (Context g a), Context g a)


gUpTrans :: Functor q => UpTrans f q g -> GUpTrans f q g
gUpTrans trans x = let (q,res) = trans x in (fmap Hole q, res)

-- | This function transforms a DUTT transition function into an
-- algebra.

gUpTransAlg :: (Functor g, Functor q)  => GUpTrans f q g -> Alg f (q (Term g), Term g)
gUpTransAlg trans = joinCxt . trans
    where joinCxt (q,r) = (fmap appCxt q, appCxt r)

-- | This function runs the given DUTT on the given term.

runGUpTrans :: (Functor f, Functor g, Functor q) => GUpTrans f q g -> Term f -> Term g
runGUpTrans trans = snd . runGUpTransSt trans

-- | This function runs the given DUTT on the given term.
runUpTrans :: (Functor f, Functor g, Functor q) => UpTrans f q g -> Term f -> Term g
runUpTrans trans = runGUpTrans (gUpTrans trans)

-- | This function is a variant of 'runUpTrans' that additionally
-- returns the final state of the run.

runGUpTransSt :: (Functor f, Functor g, Functor q) => GUpTrans f q g -> Term f -> (q (Term g), Term g)
runGUpTransSt = cata . gUpTransAlg

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.
runGUpTrans' :: (Functor f, Functor g, Functor q) => GUpTrans f q g -> Context f (q a ,a)
            -> (q (Context g a), Context g a)
runGUpTrans' trans = run where
    run (Hole (q,a)) = (fmap Hole q, Hole a)
    run (Term t) = let (q,r) = trans $ fmap run t
                   in (fmap appCxt q, appCxt r)

-- | This function composes two DUTTs.
compGUpTrans :: (Functor f, Functor g, Functor h, Functor p, Functor q)
               => GUpTrans g p h -> UpTrans f q g -> GUpTrans f (q :*: p) h
compGUpTrans t2 t1 x = ((fmap (Hole . snd) q1 :*: q2), c2) where
    (q1, c1) = t1 $ fmap (\((q1 :*: q2),a) -> (fmap (\x-> (undefined,x) ) q1,(q2,a))) x
    (q2, c2) = runGUpTrans' t2 c1
-- NB: the above construction is not correct

-- | This function composes a DUTT with an algebra.
compAlgGUpTrans :: (Functor g, Functor q)
               => Alg g a -> GUpTrans f q g -> Alg f (q a,a)
compAlgGUpTrans alg trans x = let (q,r) = trans x
                              in (fmap (cata' alg) q,cata' alg r)

-- annGUpTrans :: GUpTrans f q g -> GUpTrans f q g



type Macro f q g = forall a b . (q a, f b) -> RHS q g a b

data RHS q g a b = Con (Context g (RHS q g a b))
                 | Var a
                 | State (q (RHS q g a b),b)
