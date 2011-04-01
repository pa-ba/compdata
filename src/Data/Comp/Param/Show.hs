{-# LANGUAGE TypeOperators, FlexibleInstances, TypeSynonymInstances,
  IncoherentInstances, UndecidableInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Show
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines showing of signatures, which lifts to showing of terms.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Show
    (
     PShow(..),
     ShowD(..)
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.FreshM

-- |Printing of parametric values.
class PShow a where
    pshow :: a -> FreshM String

instance Show a => PShow a where
    pshow x = return $ show x

{-| Signature printing. An instance @ShowD f@ gives rise to an instance
  @Show (Term f)@. -}
class ShowD f where
    showD :: PShow a => f Var a -> FreshM String

instance ShowD (->) where
    showD f = do x <- genVar
                 body <- pshow $ f x
                 return $ "\\" ++ show x ++ " -> " ++ body

{-| 'ShowD' is propagated through sums. -}
instance (ShowD f, ShowD g) => ShowD (f :+: g) where
    showD (Inl x) = showD x
    showD (Inr x) = showD x

{-| From an 'ShowD' functor an 'ShowD' instance of the corresponding term type
  can be derived. -}
instance ShowD f => ShowD (Cxt f) where
    showD (Term t) = showD t
    showD (Hole h) = pshow h

instance (ShowD f, PShow a) => PShow (Cxt f Var a) where
    pshow = showD

instance (Difunctor f, ShowD f) => Show (Term f) where
    show x = evalFreshM $ showD $ toCxt x

instance (ShowD f, PShow p) => ShowD (f :&: p) where
    showD (x :&: p) = do sx <- showD x
                         sp <- pshow p
                         return $ sx ++ " :&: " ++ sp