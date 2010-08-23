{-# LANGUAGE RankNTypes #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.TermRewriting
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines term rewriting systems (TRSs) using data types
-- a la carte.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.TermRewriting where

import Data.ALaCarte
import Data.ALaCarte.Equality
import Data.Map (Map)
import Data.Maybe


{-| This type represents /recursive program schemes/.  -}

type RPS f g  = TermAlg f g

type Var = Int

{-| This type represents term rewrite rules from signature @f@ to
signature @g@ over variables of type @v@ -}

type Rule f g v = (Context f v, Context g v)


{-| This type represents term rewriting systems (TRSs) from signature
@f@ to signature @g@ over variables of type @v@.-}

type TRS f g v = [Rule f g v]

{-| This function tries to match the given rule against the given term
(resp. context in general) at the root. If successful, the function
returns the right hand side of the rule and the matching
substitution. -}

matchRule ::  (Ord v, g :<: f, FunctorEq g, FunctorEq f, Eq a)
          => Rule g g' v -> Cxt h f a -> Maybe (Context g' v, Map v (Cxt h f a))
matchRule (lhs,rhs) t = do
  subst <- match lhs t
  return (rhs,subst)

{-| This function tries to apply the given rule at the root of the
given term (resp. context in general). If successful, the function
returns the result term of the rewrite step; otherwise @Nothing@. -}

applyRule :: (Ord v, g :<: f, g' :<: f, FunctorEq g, FunctorEq f, Eq a)
          => Rule g g' v -> Cxt h f a -> Maybe (Cxt h f a)
applyRule rule t = do 
  (res, subst) <- matchRule rule t
  return $ applyCxt' res subst

{-| This function tries to apply one of the rules in the given TRS at
the root of the given term (resp. context in general) by trying each
rule one by one using 'applyRule' until one rule is applicable. If no
rule is applicable @Nothing@ is returned. -}

applyTRS :: (Ord v, g :<: f, g' :<: f, FunctorEq g, FunctorEq f, Eq a)
         => TRS g g' v -> Cxt h f a -> Maybe (Cxt h f a)
applyTRS trs t = listToMaybe $ catMaybes $ map (`applyRule` t) trs