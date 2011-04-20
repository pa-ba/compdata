{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Parsing
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- From Parse Tree to Parametric Higher-Order Abstract Syntax
--
-- The example illustrates how to convert a parse tree with explicit variables
-- into an AST which uses parametric higher-order abstract syntax instead. The
-- example shows how we can easily convert object language binders to Haskell
-- binders, without having to worry about capture avoidance.
--
--------------------------------------------------------------------------------

module Examples.Param.Parsing where

import Data.Comp.Param hiding (Const)
import Data.Comp.Param.Show ()
import Data.Comp.Param.Derive
import Data.Comp.Param.Ditraversable

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Control.Monad.Reader

type VarId = String

-- Signatures for values and operators
data Const a e = Const Int
data Abs a e = Abs VarId e
data Var a e = Var VarId
data Lam a e = Lam (a -> e) -- Note: not e -> e
data App a e = App e e
data Op a e = Add e e | Mult e e

-- Signature for the simple expression language, parse tree
type Sig = Const :+: Abs :+: Var :+: App :+: Op
-- Signature for the simple expression language, PHOAS (Lam replaces Abs + Var)
type Sig' = Const :+: Lam :+: App :+: Op

-- Derive boilerplate code using Template Haskell
$(derive [instanceDifunctor, instanceEqD, instanceShowD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op, ''Abs, ''Var])
$(derive [instanceFoldable, instanceTraversable]
         [''Const, ''App, ''Op, ''Abs, ''Var])

type TransM = Reader (Map VarId Any)

class PHOASTrans f g where
  transAlg :: Alg f (TransM (Term g))

$(derive [liftSum] [''PHOASTrans])

-- default translation
instance (f :<: g, Ditraversable f TransM Any) => PHOASTrans f g where
  transAlg x =  liftM inject $ disequence $ dimap (return . Place) id x

instance (Lam :<: g) => PHOASTrans Abs g where
  transAlg (Abs x b) = do env <- ask
                          return $ iLam $ \y -> runReader b (Map.insert x y env)

instance PHOASTrans Var g where
  transAlg (Var x) = liftM (Place . fromJust) $ asks $ Map.lookup x

trans :: Term Sig -> Term Sig'
trans x = runReader (cata transAlg x) Map.empty

-- Example: evalEx = iLam $ \a -> iApp (iLam $ \b -> iLam $ \c -> hole b) (hole a)
transEx :: Term Sig'
transEx = trans $ iAbs "y" $ (iAbs "x" $ iAbs "y" $ iVar "x") `iApp` (iVar "y")