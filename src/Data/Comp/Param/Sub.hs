{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances,
  IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Sub
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the subtyping relation @:<@.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Sub
    (
     (:<)(..)
    ) where

{-| Subtyping relation. An instance @a :< b@ means that values of type @a@ can
 be coerced to values of type @b@. -}
class a :< b where
    coerce :: a -> b

instance (:<) a a where
    coerce = id

instance (Monad m, a :< b) => (:<) a (m b) where
    coerce = return . coerce