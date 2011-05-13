{-# LANGUAGE EmptyDataDecls #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Any
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

module Data.Comp.Param.Any
    (
     Any
    ) where

-- |The empty data type 'Any' is used to emulate parametricity
-- (\"poor mans parametricity\").
data Any