{-# LANGUAGE RankNTypes #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Automata
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines tree automata based on data types a la carte
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Automata where

import Data.ALaCarte
import Data.Maybe
import Data.Traversable
import Control.Monad


{-| This type represents transition functions of deterministic
bottom-up tree acceptors (DUTAs).  -}

type DUTATrans f q = Alg f q

{-| This data type represents deterministic bottom-up tree acceptors (DUTAs).
-}
data DUTA f q = DUTA {
      dutaTrans :: DUTATrans f q,
      dutaAccept :: q -> Bool
    }

{-| This function runs the transition function of a DUTA on the given
term. -}

runDUTATrans :: Functor f => DUTATrans f q -> Term f -> q
runDUTATrans = cata

{-| This function checks whether a given DUTA accepts a term.  -}

duta :: Functor f => DUTA f q -> Term f -> Bool
duta DUTA{dutaTrans = trans, dutaAccept = accept} = accept . runDUTATrans trans



{-| This type represents transition functions of non-deterministic
bottom-up tree acceptors (NUTAs).  -}

type NUTATrans f q = AlgM [] f q


{-| This type represents non-deterministic bottom-up tree acceptors.
-}
data NUTA f q = NUTA {
      nutaTrans :: AlgM [] f q,
      nutaAccept :: q -> Bool
    }

{-| This function runs the given transition function of a NUTA on the
given term -}

runNUTATrans :: Traversable f => NUTATrans f q -> Term f -> [q]
runNUTATrans = cataM

{-| This function checks whether a given NUTA accepts a term. -}

nuta :: Traversable f => NUTA f q -> Term f -> Bool
nuta NUTA{nutaTrans = trans, nutaAccept = accept} = any accept . runNUTATrans trans


{-| This function determinises the given NUTA.  -}

determNUTA :: (Traversable f) => NUTA f q -> DUTA f [q]
determNUTA n = DUTA{
               dutaTrans = algM $ nutaTrans n,
               dutaAccept = any $ nutaAccept n}

{-| This function represents transition functions of
deterministic bottom-up tree transducers (DUTTs).  -}

type DUTTTrans f g q = forall a. f (q,a) -> (q, Cxt Hole g a)

{-| This function transforms a DUTT transition function into an
algebra.  -}

duttTransAlg :: (Functor f, Functor g)  => DUTTTrans f g q -> Alg f (q, Term g)
duttTransAlg trans = fmap injectCxt . trans 

{-| This function runs the given DUTT transition function on the given
term.  -}

runDUTTTrans :: (Functor f, Functor g)  => DUTTTrans f g q -> Term f -> (q, Term g)
runDUTTTrans = cata . duttTransAlg

{-| This data type represents deterministic bottom-up tree
transducers. -}

data DUTT f g q = DUTT {
      duttTrans :: DUTTTrans f g q,
      duttAccept :: q -> Bool
    }

{-| This function transforms the given term according to the given
DUTT and returns the resulting term provided it is accepted by the
DUTT. -}

dutt :: (Functor f, Functor g) => DUTT f g q -> Term f -> Maybe (Term g)
dutt DUTT{duttTrans = trans, duttAccept = accept} = accept' . runDUTTTrans trans
    where accept' (q,res)
              | accept q = Just res
              | otherwise = Nothing

{-| This type represents transition functions of non-deterministic
bottom-up tree transducers (NUTTs).  -}

type NUTTTrans f g q = forall a. f (q,a) -> [(q, Cxt Hole g a)]

{-| This function transforms a NUTT transition function into a monadic
algebra.  -}

nuttTransAlg :: (Functor f, Functor g)  => NUTTTrans f g q -> AlgM [] f (q, Term g)
nuttTransAlg trans = liftM (fmap injectCxt) . trans 

{-| This function runs the given NUTT transition function on the given
term.  -}

runNUTTTrans :: (Traversable f, Functor g)  => NUTTTrans f g q -> Term f -> [(q, Term g)]
runNUTTTrans = cataM . nuttTransAlg

{-| This data type represents non-deterministic bottom-up tree
transducers (NUTTs). -}

data NUTT f g q = NUTT {
      nuttTrans :: NUTTTrans f g q,
      nuttAccept :: q -> Bool
    }

{-| This function transforms the given term according to the given
NUTT and returns a list containing all accepted results. -}

nutt :: (Traversable f, Functor g) => NUTT f g q -> Term f -> [Term g]
nutt NUTT{nuttTrans = trans, nuttAccept = accept} = catMaybes . map accept' . runNUTTTrans trans
    where accept' (q,res)
              | accept q = Just res
              | otherwise = Nothing