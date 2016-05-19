{-# LANGUAGE GADTs      #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.TermRewriting
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines term rewriting systems (TRSs) using compositional data
-- types.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.TermRewriting where

import Prelude hiding (any)

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Equality
import Data.Comp.Multi.Matching
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Term
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.Ordering
import Data.Comp.Multi.Ops
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Unsafe.Coerce
import Control.Monad


{-| This type represents /recursive program schemes/.  -}

type RPS f g  = Hom f g

-- | This type represents variables.
type Var = Int

{-| This type represents term rewrite rules from signature @f@ to
signature @g@ over variables of type @v@ -}

type Rule f g v i = (Context f v i, Context g v i)


{-| This type represents term rewriting systems (TRSs) from signature
@f@ to signature @g@ over variables of type @v@. -}

type TRS f g v i = [Rule f g v i]

-- | This type represents a potential single step reduction from any
-- input.
type Step t = t -> Maybe t
-- | This type represents a potential single step reduction from any
-- input. If there is no single step then the return value is the
-- input together with @False@. Otherwise, the successor is returned
-- together with @True@.
type BStep t = t -> (t,Bool)

{-| This function tries to match the given rule against the given term
(resp. context in general) at the root. If successful, the function
returns the right hand side of the rule and the matching
substitution. -}

matchRule ::  (KOrd v, KEq a, EqHF f, HFunctor f, HFoldable f)
          => Rule f g v i -> Cxt h f a i -> Maybe (Context g v i, Map (E v) (E (Cxt h f a)))
matchRule (lhs,rhs) t = do
  subst <- matchCxt lhs t
  return (rhs,subst)

-- | This function tries to match the rules of the given TRS against
-- the given term (resp. context in general) at the root. The first
-- rule in the TRS that matches is then used and the corresponding
-- right-hand side as well the matching substitution is returned.
matchRules :: (KOrd v, KEq a, EqHF f, HFunctor f, HFoldable f)
           => TRS f g v i -> Cxt h f a i -> Maybe (Context g v i, Map (E v) (E (Cxt h f a)))
matchRules trs t = listToMaybe $ mapMaybe (`matchRule` t) trs


{-| This function tries to apply the given rule at the root of the
given term (resp. context in general). If successful, the function
returns the result term of the rewrite step; otherwise @Nothing@. -}

appRule :: (EqHF f, HFunctor f, HFoldable f,KEq a,KOrd v)
          => Rule f f v i -> Cxt h f a i -> Maybe (E (Cxt h f a))
appRule rule t = do
  (res, subst) <- matchRule rule t
  return $ flip substHoles' subst res

substHoles' :: (HFunctor f, HFunctor g, f :<: g, KOrd v) =>
    Cxt h' f v i -> Map (E v) (E (Cxt h g a)) -> E (Cxt h g a)
substHoles' c m = E $ substHoles (t m) c

t :: KOrd v => Map (E v) (E (Cxt h g a)) -> (v :-> Cxt h g a)
t m = (\v -> (\case {E a -> unsafeCoerce a}) . fromJust $ Map.lookup (E v) m)


{-| This function tries to apply one of the rules in the given TRS at
the root of the given term (resp. context in general) by trying each
rule one by one using 'appRule' until one rule is applicable. If no
rule is applicable @Nothing@ is returned. -}
appTRS :: (KEq a,KOrd v,EqHF f, HFunctor f, HFoldable f)
         => TRS f f v i -> Cxt h f a i -> E (HMaybe (Cxt h f a))
appTRS trs t = listToHMaybe $ mapMaybe (`appRule` t) trs
    where
        listToHMaybe [] = E HNothing
        listToHMaybe (E a:_) = E $ HJust a


{-| This is an auxiliary function that turns function @f@ of type
  @(t -> Maybe t)@ into functions @f'@ of type @t -> (t,Bool)@. @f' x@
  evaluates to @(y,True)@ if @f x@ evaluates to @Just y@, and to
  @(x,False)@ if @f x@ evaluates to @Nothing@. This function is useful
  to change the output of functions that apply rules such as 'appTRS'. -}

bStep :: Step t -> BStep t
bStep f t = case f t of
                Nothing -> (t, False)
                Just t' -> (t',True)

{-| This function performs a parallel reduction step by trying to
apply rules of the given system to all outermost redexes. If the given
term contains no redexes, @Nothing@ is returned. -}
newtype HBool i = HBool {unHBool::Bool}
parTopStep :: forall h f a i v. (KEq a,KOrd v,EqHF f, HFoldable f, HFunctor f)
           => TRS f f v i -> E (Cxt h f a) -> E (HMaybe ((Cxt h f a)))
parTopStep _ (E Hole{}) = E HNothing
parTopStep trs (E c@(Term t)) = tTop `hemplus` tBelow'
    where
          tTop :: E (HMaybe (Cxt h f a))
          tTop = appTRS trs (unsafeCoerce c)
          tBelow' :: E (HMaybe (Cxt h f a))
          tBelow'
              -- = undefined
              -- {-
              | tAny = E $ HJust $ Term $ hfmap (\(P a _) -> a) tBelow
              | otherwise = E HNothing
          tBelow = hfmap (  (hbStep $ ((\(E a) -> unsafeCoerce a) .parTopStep trs . E)) ) t
          tAny :: Bool
          tAny = (\(P _ a) -> a) $ hfoldr (\(P _ a) (P b c) -> P b (a || c)) (P undefined False) tBelow
              ---}
             
toHMaybe (Just a) = HJust a 
toHMaybe Nothing = HNothing
data HMaybe a i = HNothing | HJust (a i)
hemplus :: E (HMaybe a) -> E (HMaybe a) -> E (HMaybe a)
hemplus (E HNothing) f = f
hemplus f@(E _) _ = f
hmplus :: HMaybe a i -> HMaybe a i -> HMaybe a i
hmplus HNothing f = f
hmplus f _ = f
data HPair a i = P (a i) Bool
hbStep :: (t i -> HMaybe t i) -> t i -> HPair t i
hbStep f t = case f t of
                HNothing -> P t False
                HJust t' -> P t' True

{-| This function performs a parallel reduction step by trying to
apply rules of the given system to all outermost redexes and then
recursively in the variable positions of the redexes. If the given
term does not contain any redexes, @Nothing@ is returned. -}

{-
parallelStep :: (Ord (v i), EqHF f,HFoldable f, HFunctor  f)
             => TRS f f v i -> Step (Cxt h f a i)
parallelStep _ Hole{} = Nothing
parallelStep trs c@(Term t) =
    case matchRules trs c of
      Nothing
          | anyBelow -> Just $ Term $ fmap fst below
          | otherwise -> Nothing
        where below = fmap (bStep $ parallelStep trs) t
              anyBelow = any snd below
      Just (rhs,subst) -> Just $ substHoles' rhs substBelow
          where rhsVars = Set.fromList $ toList rhs
                substBelow = Map.mapMaybeWithKey apply subst
                apply v t
                    | Set.member v rhsVars = Just $ fst $ bStep (parallelStep trs) t
                    | otherwise = Nothing

-}

{-| This function applies the given reduction step repeatedly until a
normal form is reached. -}

reduce :: Step t -> t -> t
reduce s t = case s t of
               Nothing -> t
               Just t' -> reduce s t'
