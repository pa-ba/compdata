--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use compositional data
-- types for mutually recursive data types. Examples of usage are provided
-- below.
--
--------------------------------------------------------------------------------
module Data.Comp.Multi (
  -- * Examples
  -- ** Mutually Recursive Compositional Data Types
  -- $ex1

  -- ** Generalised Compositional Data Types (GADTs for Compositional Data Types)
  -- $ex2
    module Data.Comp.Multi.Term
  , module Data.Comp.Multi.Algebra
  , module Data.Comp.Multi.HFunctor
  , module Data.Comp.Multi.Sum
  , module Data.Comp.Multi.Product
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Product

{- $ex1
The example below illustrates how to use mutually recursive compositional data
types to implement a small expression language, with a sub language of values,
and an evaluation function mapping expressions to values.

The following language extensions are
needed in order to run the example: @TemplateHaskell@, @TypeOperators@,
@MultiParamTypeClasses@, @FlexibleInstances@, @FlexibleContexts@,
@UndecidableInstances@, @GADTs@, and @EmptyDataDecls@.

> TODO
-}

{- $ex2
The example below illustrates how to use generalised compositional data
types to implement a small expression language, with a sub language of values,
and an evaluation function mapping expressions to values.

The following language extensions are
needed in order to run the example: @TemplateHaskell@, @TypeOperators@,
@MultiParamTypeClasses@, @FlexibleInstances@, @FlexibleContexts@,
@UndecidableInstances@, @GADTs@, and @EmptyDataDecls@.

> TODO
-}