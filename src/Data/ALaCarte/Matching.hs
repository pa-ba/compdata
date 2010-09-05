{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Matching
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module implements matching of contexts or terms with variables againts terms
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Matching
    (
     matchCxt,
     matchTerm
    ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Equality
import Data.ALaCarte.Variables
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable

import Prelude hiding (mapM_, all)

{-| This is an auxiliary function for implementing 'matchCxt'. It behaves
similarly as 'match' but is oblivious to non-linearity. Therefore, the
substitution that is returned maps holes to non-empty lists of terms
(resp. contexts in general). This substitution is only a matching
substitution if all elements in each list of the substitution's range
are equal. -}

matchCxt' :: (Ord v, EqF f, Functor f, Foldable f)
       => Context f v -> Cxt h f a -> Maybe (Map v [Cxt h f a])
matchCxt' (Hole v) t = Just $  Map.singleton v [t]
matchCxt' (Term s) (Term t) = do
  eqs <- eqMod s t
  substs <- mapM (uncurry matchCxt') eqs
  return $ Map.unionsWith (++) substs
matchCxt' Term {} Hole {} = Nothing


{-| This function takes a context @c@ as the first argument and tries
to match it against the term @t@ (or in general a context with holes
in @a@). The context @c@ matches the term @t@ if there is a /matching
substitution/ @s@ that maps holes to terms (resp. contexts in general)
such that if the holes in the context @c@ are replaced according to
the substitution @s@, the term @t@ is obtained. Note that the context
@c@ might be non-linear, i.e. has multiple holes that are
equal. According to the above definition this means that holes with
equal holes have to be instantiated by equal terms! -}

matchCxt :: (Ord v,EqF f, Eq (Cxt h f a), Functor f, Foldable f)
         => Context f v -> Cxt h f a -> Maybe (Map v (Cxt h f a))
matchCxt c1 c2 = do 
  res <- matchCxt' c1 c2
  let insts = Map.elems res
  mapM_ checkEq insts
  return $ Map.map head res
    where checkEq [] = Nothing
          checkEq (c : cs)
              | all (== c) cs = Just ()
              | otherwise = Nothing

{-| This function is similar to 'matchCxt' but instead of a context it
matches a term with variables against a context.  -}

matchTerm :: (Ord v, EqF f, Eq (Cxt h f a) , Functor f, Foldable f, HasVars f v)
          => Term f -> Cxt h f a -> Maybe (Map v (Cxt h f a))
matchTerm t c = matchCxt (varsToHoles t) c