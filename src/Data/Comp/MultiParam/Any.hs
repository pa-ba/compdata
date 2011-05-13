{-# LANGUAGE EmptyDataDecls, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Any
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the empty data type 'Any', which is used to emulate
-- parametricity (\"poor mans parametricity\").
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Any
    (
     Any
    ) where

-- |The empty data type 'Any' is used to emulate parametricity
-- (\"poor mans parametricity\").
data Any :: * -> *