{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, IncoherentInstances, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Automata.Product
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.Automata.Product ((:<)(..)) where

import Data.Comp.Automata.Product.Derive


instance a :< a where
    get = id

$(genAllInsts 7)

instance (c :< b) => c :< (a,b) where
    get = get . snd