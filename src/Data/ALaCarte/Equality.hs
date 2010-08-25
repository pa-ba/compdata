{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Equality
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- The equality algebra (equality on terms).
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Equality
    (
     EqF(..),
     deriveEqF,
     deriveEqFs,
     match,
    ) where

import Data.ALaCarte
import Data.ALaCarte.Derive.Utils
import Data.ALaCarte.Derive.Equality
import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map


instance (EqF f, Eq p) => EqF (f :*: p) where
    eqMod (v1 :*: p1) (v2 :*: p2) = unless (p1 == p2) mzero
                                    >> eqMod v1 v2
    eqAlg (v1 :*: p1) (v2 :*: p2) = p1 == p2 && v1 `eqAlg` v2

{-|
  'EqF' is propagated through sums.
-}

instance (EqF f, EqF g) => EqF (f :+: g) where
    eqMod (Inl x) (Inl y) = eqMod x y
    eqMod (Inr x) (Inr y) = eqMod x y
    eqMod _ _ = Nothing

    eqAlg (Inl x) (Inl y) = eqAlg x y
    eqAlg (Inr x) (Inr y) = eqAlg x y
    eqAlg _ _ = False

{-|
  From an 'EqF' functor an 'Eq' instance of the corresponding
  term type can be derived.
-}
instance (EqF f) => EqF (Cxt h f) where
    eqMod (Term e1) (Term e2) = liftM concat $
                                eqMod e1 e2 >>= mapM (uncurry eqMod)
    eqMod (Hole h1) (Hole h2) = Just [(h1,h2)]
    eqMod _ _ = Nothing

    eqAlg (Term e1) (Term e2) = e1 `eqAlg` e2
    eqAlg (Hole h1) (Hole h2) = h1 == h2
    eqAlg _ _ = False

instance (EqF f, Eq a)  => Eq (Cxt h f a) where
    (==) = eqAlg

instance EqF [] where
    eqMod [] [] = Just []
    eqMod (x:xs) (y:ys) = do
                  res <- eqMod xs ys
                  return $ (x,y) : res
    eqMod _ _ = Nothing
    eqAlg = (==)

{-| This is an auxiliary function for implementing 'match'. It behaves
similarly as 'match' but is oblivious to non-linearity. Therefore, the
substitution that is returned maps holes to non-empty lists of terms
(resp. contexts in general). This substitution is only a matching
substitution if all elements in each list of the substitution's range
are equal. -}

match' :: (Ord v,f :<: g, EqF f) => Context f v -> Cxt h g a -> Maybe (Map v [Cxt h g a])
match' (Hole v) t = Just $  Map.singleton v [t]
match' (Term s) t = do
  t' <- project t
  eqs <- eqMod s t'
  substs <- mapM (uncurry match') eqs
  return $ Map.unionsWith (++) substs


{-| This function takes a context @c@ as the first argument and tries
to match it against the term @t@ (or in general a context with holes
in @a@). The context @c@ matches the term @t@ if there is a /matching
substitution/ @s@ that maps holes to terms (resp. contexts in general)
such that if the holes in the context @c@ are replaced according to
the substitution @s@, the term @t@ is obtained. Note that the context
@c@ might be non-linear, i.e. has multiple holes that are
equal. According to the above definition this means that holes with
equal holes have to be instantiated by equal terms! -}

match :: (Ord v,f :<: g, EqF f, Eq (Cxt h g a))
         => Context f v -> Cxt h g a -> Maybe (Map v (Cxt h g a))
match c1 c2 = do 
  res <- match' c1 c2
  let insts = Map.elems res
  mapM_ checkEq insts
  return $ Map.map head res
    where checkEq [] = Nothing
          checkEq (c : cs)
              | all (== c) cs = Just ()
              | otherwise = Nothing


$(deriveEqFs $ [''Maybe] ++ tupleTypes 2 10)