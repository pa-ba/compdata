{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Multi.HFunctor
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr
-- Stability   :  unknown
-- Portability :  unknown
--
-- This module defines higher-order functors (Johann, Ghani, POPL
-- '08), i.e. endofunctors on the category of endofunctors.
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Multi.HFunctor
    (
     HFunctor (..),
     HFoldable (..),
     HTraversable (..),
     (:->),
     (:=>),
     NatM,
     NatC
     ) where

import Data.Typeable


infixr 0 :-> -- same precedence as function space operator ->
infixr 0 :=> -- same precedence as function space operator ->

-- | This type represents natural transformations.
type f :-> g = forall i . Typeable i => f i -> g i

-- | This type represents co-cones from @f@ to @a@. @f :=> a@ is
-- isomorphic to f :-> K a
type f :=> a = forall i . Typeable i => f i -> a


type NatM m f g = forall i. Typeable i => f i -> m (g i)

type NatC c = forall i. Typeable i => c i

-- | This class represents higher-order functors (Johann, Ghani, POPL
-- '08) which are endofunctors on the category of endofunctors.
class HFunctor h where
    -- A higher-order functor @f@ maps every functor @g@ to a
    -- functor @f g@.
    --
    -- @ffmap :: (Functor g) => (a -> b) -> f g a -> f g b@
    -- 
    -- We omit this, as it does not work for GADTs (see Johand and
    -- Ghani 2008).

    -- | A higher-order functor @f@ also maps a natural transformation
    -- @g :-> h@ to a natural transformation @f g :-> f h@
    hfmap :: (f :-> g) -> h f :-> h g


class HFunctor h => HFoldable h where
    hfoldr :: (a :=> b -> b) -> b -> h a :=> b
    hfoldl :: (b -> a :=> b) -> b -> h a :=> b
    

class HFoldable t => HTraversable t where

    -- | Map each element of a structure to a monadic action, evaluate
    -- these actions from left to right, and collect the results.
    --
    -- Alternative type in terms of natural transformations using
    -- functor composition @:.:@:
    --
    -- @hmapM :: Monad m => (a :-> m :.: b) -> t a :-> m :.: (t b)@
    hmapM :: (Monad m) => NatM m a b -> NatM m (t a) (t b)
