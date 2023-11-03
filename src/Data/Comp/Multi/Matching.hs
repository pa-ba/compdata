{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Matching
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements matching of contexts or terms with variables againts terms
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Matching
    (
     matchCxt,
     matchTerm,
     module Data.Comp.Multi.Variables
    ) where

import Data.Comp.Multi.Equality
import Data.Comp.Multi.Term
import Data.Comp.Multi.Variables
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.Ordering
import Data.Foldable
import Data.Map (Map,mapKeys)
import qualified Data.Map as Map
import Data.Traversable

import Prelude hiding (all, mapM, mapM_)

{-| This is an auxiliary function for implementing 'matchCxt'. It behaves
similarly as 'match' but is oblivious to non-linearity. Therefore, the
substitution that is returned maps holes to non-empty lists of terms
(resp. contexts in general). This substitution is only a matching
substitution if all elements in each list of the substitution's range
are equal. -}


heqMod' :: (EqHF f, HFunctor f, HFoldable f) => f a i -> f b j -> Maybe [(E a, E b)]
heqMod' s t
    | unit s `eqHF` unit' t = Just args
    | otherwise = Nothing
    where unit = hfmap (const $ K ())
          unit' = hfmap (const $ K ())
          args = htoList s `zip` htoList t
          
{-
-}
matchCxt' :: (KOrd v,EqHF f,HFoldable f) => E (Context f v ) -> E (Cxt h f a)
            -> Maybe (Map (E v) [E (Cxt h f a)])
matchCxt' (E (Hole v)) ( t) = Just $  Map.singleton (E v) [( t)]
matchCxt' (E (Term s)) (E (Term t)) = do
  eqs <- heqMod' s t
  substs <- mapM (uncurry matchCxt') eqs
  return $ Map.unionsWith (++) substs
matchCxt' (E (Term _)) (E (Hole _)) = Nothing
{-
-}



{-| This function takes a context @c@ as the first argument and tries
to match it against the term @t@ (or in general a context with holes
in @a@). The context @c@ matches the term @t@ if there is a
/matching substitution/ @s@ that maps holes to terms (resp. contexts in general)
such that if the holes in the context @c@ are replaced according to
the substitution @s@, the term @t@ is obtained. Note that the context
@c@ might be non-linear, i.e. has multiple holes that are
equal. According to the above definition this means that holes with
equal holes have to be instantiated by equal terms! -}

matchCxt :: (HFoldable f,EqHF f,KOrd v,KEq a) => Context f v i
                    -> Cxt h f a i1 -> Maybe (Map (E v) (E (Cxt h f a)))
matchCxt c1 c2 = do
  res <- matchCxt' (E c1) (E c2)
  let insts = Map.elems res
  mapM_ checkEq insts
  return $ Map.map (head) res
    where checkEq [] = Nothing
          checkEq (c : cs)
              | all (== c) cs = Just ()
              | otherwise = Nothing

{-| This function is similar to 'matchCxt' but instead of a context it
matches a term with variables against a context.  -}

matchTerm :: (KEq a,Ord (v i),KOrd v, EqHF f, Eq (Cxt h f a i) , HTraversable f, HasVars f (v i))
          => Term f i -> Cxt h f a i -> Maybe (Map (v i) (E (Cxt h f a)))
matchTerm t c = do
    res <- matchCxt (varsToHoles t) c
    return $ mapKeys (\(E (K a)) -> a) res
