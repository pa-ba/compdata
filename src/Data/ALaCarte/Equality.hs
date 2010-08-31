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
     matchCxt,
     eqMod,
    ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Sum
import Data.ALaCarte.Derive.Utils
import Data.ALaCarte.Derive

import Data.Foldable

import Control.Monad hiding (mapM_)
import Prelude hiding (mapM_, all)

import Data.Map (Map)
import qualified Data.Map as Map


-- instance (EqF f, Eq p) => EqF (f :*: p) where
--    eqF (v1 :*: p1) (v2 :*: p2) = p1 == p2 && v1 `eqF` v2

{-|
  'EqF' is propagated through sums.
-}

instance (EqF f, EqF g) => EqF (f :+: g) where
    eqF (Inl x) (Inl y) = eqF x y
    eqF (Inr x) (Inr y) = eqF x y
    eqF _ _ = False

instance EqF NilF where
    eqF _ _ = True

{-|
  From an 'EqF' functor an 'Eq' instance of the corresponding
  term type can be derived.
-}
instance (EqF f) => EqF (Cxt h f) where

    eqF (Term e1) (Term e2) = e1 `eqF` e2
    eqF (Hole h1) (Hole h2) = h1 == h2
    eqF _ _ = False

instance (EqF f, Eq a)  => Eq (Cxt h f a) where
    (==) = eqF

instance EqF [] where
    eqF = (==)

{-| This function implements equality of values of type @f a@ modulo
the equality of @a@ itself. If two functorial values are equal in this
sense, 'eqMod' returns a 'Just' value containing a list of pairs
consisting of corresponding components of the two functorial
values. -}

eqMod :: (EqF f, Functor f, Foldable f) => f a -> f b -> Maybe [(a,b)]
eqMod s t
    | unit s `eqF` unit t = Just args
    | otherwise = Nothing
    where unit = fmap (const ())
          args = toList s `zip` toList t
          

{-| This is an auxiliary function for implementing 'matchCxt'. It behaves
similarly as 'match' but is oblivious to non-linearity. Therefore, the
substitution that is returned maps holes to non-empty lists of terms
(resp. contexts in general). This substitution is only a matching
substitution if all elements in each list of the substitution's range
are equal. -}

matchCxt' :: (Ord v,f :<: g, EqF f, Functor f, Foldable f)
       => Context f v -> Cxt h g a -> Maybe (Map v [Cxt h g a])
matchCxt' (Hole v) t = Just $  Map.singleton v [t]
matchCxt' (Term s) t = do
  t' <- project t
  eqs <- eqMod s t'
  substs <- mapM (uncurry matchCxt') eqs
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

matchCxt :: (Ord v,f :<: g, EqF f, Eq (Cxt h g a), Functor f, Foldable f)
         => Context f v -> Cxt h g a -> Maybe (Map v (Cxt h g a))
matchCxt c1 c2 = do 
  res <- matchCxt' c1 c2
  let insts = Map.elems res
  mapM_ checkEq insts
  return $ Map.map head res
    where checkEq [] = Nothing
          checkEq (c : cs)
              | all (== c) cs = Just ()
              | otherwise = Nothing


$(derive [instanceEqF] $ [''Maybe] ++ tupleTypes 2 10)