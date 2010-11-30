{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell #-}
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
     eqMod,
    ) where

import Data.ALaCarte.Term
import Data.ALaCarte.Sum
import Data.ALaCarte.Derive
import Data.ALaCarte.Derive.Utils

import Data.Foldable

import Control.Monad hiding (mapM_)
import Prelude hiding (mapM_, all)



-- instance (EqF f, Eq p) => EqF (f :*: p) where
--    eqF (v1 :*: p1) (v2 :*: p2) = p1 == p2 && v1 `eqF` v2

{-|
  'EqF' is propagated through sums.
-}

instance (EqF f, EqF g) => EqF (f :+: g) where
    eqF (Inl x) (Inl y) = eqF x y
    eqF (Inr x) (Inr y) = eqF x y
    eqF _ _ = False

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

$(derive [instanceEqF] $ [''Maybe] ++ tupleTypes 2 10)