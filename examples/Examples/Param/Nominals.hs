{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Nominals
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- From nominals to parametric higher-order abstract syntax and back
--
-- The example illustrates how to convert a parse tree with explicit nominal
-- variables into an AST that uses parametric higher-order abstract syntax,
-- and back again. The example shows how we can easily convert object language
-- binders to Haskell binders, without having to worry about capture avoidance.
--
--------------------------------------------------------------------------------

module Examples.Param.Nominals where

import Data.Comp.Param hiding (Var)
import qualified Data.Comp.Param as P
import Data.Comp.Param.Derive
import Data.Comp.Param.Ditraversable
import Data.Comp.Param.Show ()
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad.Reader

data Lam a b   = Lam (a -> b)
data App a b   = App b b
data Const a b = Const Int
data Plus a b  = Plus b b
type Nom       = String                 -- The type of nominals
data NLam a b  = NLam Nom b
data NVar a b  = NVar Nom
type SigB      = App :+: Const :+: Plus
type SigN      = NLam :+: NVar :+: SigB -- The nominal signature
type SigP      = Lam :+: SigB           -- The PHOAS signature

$(derive [makeDifunctor, makeShowD, makeEqD, smartConstructors]
         [''Lam, ''App, ''Const, ''Plus, ''NLam, ''NVar])
$(derive [makeDitraversable]
         [''App, ''Const, ''Plus, ''NLam, ''NVar])


--------------------------------------------------------------------------------
-- Nominal to PHOAS translation
--------------------------------------------------------------------------------

type M f a = Reader (Map.Map Nom (Trm f a))

class N2PTrans f g where
  n2pAlg :: Alg f (M g a (Trm g a))

$(derive [liftSum] [''N2PTrans])

n2p :: (Difunctor f, N2PTrans f g) => Term f -> Term g
n2p t = Term $ runReader (cata n2pAlg t) Map.empty

instance (Lam :<: g) => N2PTrans NLam g where
  n2pAlg (NLam x b) = do vars <- ask
                         return $ iLam $ \y -> runReader b (Map.insert x y vars)

instance (Ditraversable f, f :<: g) => N2PTrans f g where
  n2pAlg = liftM inject . disequence . dimap (return . P.Var) id -- default

instance N2PTrans NVar g where
  n2pAlg (NVar x) = liftM fromJust (asks (Map.lookup x))

en :: Term SigN
en = Term $ iNLam "x1" $ iNLam "x2" (iNLam "x3" $ iNVar "x2") `iApp` iNVar "x1"

ep :: Term SigP
ep = n2p en


--------------------------------------------------------------------------------
-- PHOAS to nominal translation
--------------------------------------------------------------------------------

type M' = Reader [Nom]

class P2NTrans f g where
  p2nAlg :: Alg f (M' (Trm g a))

$(derive [liftSum] [''P2NTrans])

p2n :: (Difunctor f, P2NTrans f g) => Term f -> Term g
p2n t = Term $ runReader (cata p2nAlg t) ['x' : show n | n <- [1..]]

instance (Ditraversable f, f :<: g) => P2NTrans f g where
  p2nAlg = liftM inject . disequence . dimap (return . P.Var) id -- default

instance (NLam :<: g, NVar :<: g) => P2NTrans Lam g where
  p2nAlg (Lam f) = do n:noms <- ask
                      return $ iNLam n (runReader (f (return $ iNVar n)) noms)

ep' :: Term SigP
ep' = Term $ iLam $ \a -> iLam (\b -> (iLam $ \a -> b)) `iApp` a

en' :: Term SigN
en' = p2n ep'