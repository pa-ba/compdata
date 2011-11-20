{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.FreshM
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines a monad for generating fresh, abstract names, useful
-- e.g. for defining equality on terms.
--
--------------------------------------------------------------------------------
module Data.Comp.MultiParam.FreshM
    (
     FreshM,
     Name,
     withName,
     nameCoerce,
     evalFreshM
    ) where

import Control.Monad.Reader

-- |Monad for generating fresh (abstract) names.
newtype FreshM a = FreshM{unFreshM :: Reader [String] a}
    deriving Monad

-- |Abstract notion of a name (the constructor is hidden).
data Name i = Name String
              deriving Eq

instance Show (Name i) where
    show (Name x) = x

instance Ord (Name i) where
    compare (Name x) (Name y) = compare x y

-- |Change the type tag of a name.
nameCoerce :: Name i -> Name j
nameCoerce (Name x) = Name x

-- |Run the given computation with the next available name.
withName :: (Name i -> FreshM a) -> FreshM a
withName m = do name <- FreshM (asks (Name . head))
                FreshM $ local tail $ unFreshM $ m name

-- |Evaluate a computation that uses fresh names.
evalFreshM :: FreshM a -> a
evalFreshM (FreshM m) = runReader m names
    where baseNames = ['a'..'z']
          names = map (:[]) baseNames ++ names' 1
          names' n = map (: show n) baseNames ++ names' (n + 1)