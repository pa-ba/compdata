{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.FreshM
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
module Data.Comp.Param.FreshM
    (
     FreshM,
     Name,
     withName,
     evalFreshM
    ) where

import Control.Monad.Reader

-- |Monad for generating fresh (abstract) names.
newtype FreshM a = FreshM{unFreshM :: Reader [String] a}
    deriving Monad

-- |Abstract notion of a name (the constructor is hidden).
data Name = Name String
            deriving Eq

instance Show Name where
    show (Name x) = x

instance Ord Name where
    compare (Name x) (Name y) = compare x y

-- |Run the given computation with the next available name.
withName :: (Name -> FreshM a) -> FreshM a
withName m = do nom <- FreshM (asks (Name . head))
                FreshM $ local tail $ unFreshM $ m nom

-- |Evaluate a computation that uses fresh names.
evalFreshM :: FreshM a -> a
evalFreshM (FreshM m) = runReader m noms
    where baseNames = ['a'..'z']
          noms = map (:[]) baseNames ++ noms' 1
          noms' n = map (: show n) baseNames ++ noms' (n + 1)