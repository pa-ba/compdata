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
-- This module defines a monad for generating fresh, abstract nominals, useful
-- e.g. for defining equality on terms.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.FreshM
    (
     FreshM,
     Nom,
     getNom,
     nextNom,
     evalFreshM
    ) where

import Control.Monad.Reader

-- |Monad for generating fresh (abstract) nominals.
newtype FreshM a = FreshM{unFreshM :: Reader [String] a}
    deriving Monad

-- |Abstract notion of a nominal (the constructor is hidden).
data Nom = Nom String
           deriving Eq

instance Show Nom where
    show (Nom x) = x

instance Ord Nom where
    compare (Nom x) (Nom y) = compare x y

-- |Get the current nominal.
getNom :: FreshM Nom
getNom = FreshM $ asks (Nom . head)

-- |Use the next available nominal in the monadic computation.
nextNom :: FreshM a -> FreshM a
nextNom = FreshM . local tail . unFreshM

-- |Evaluate a computation that uses fresh nominals.
evalFreshM :: FreshM a -> a
evalFreshM (FreshM m) = runReader m noms
    where baseNoms = ['a'..'z']
          noms = map (:[]) baseNoms ++ noms' 1
          noms' n = map (: show n) baseNoms ++ noms' (n + 1)