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
-- variables into an AST which uses parametric higher-order abstract syntax,
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

type VarId = String -- Nominals
data Val a e = Const Int | Pair e e
data Op a e  = Mult e e | Fst e | Snd e
data Abs a e = Abs VarId e
data Var a e = Var VarId -- Nominal
data Lam a e = Lam VarId (a -> e) -- The VarId is the original nominal
data App a e = App e e
type SigB    = App :+: Op :+: Val -- The base signature
type SigN    = Abs :+: Var :+: SigB -- The nominal signature
type SigP    = Lam :+: SigB -- The PHOAS signature

$(derive [makeDifunctor, makeDitraversable, makeShowD, makeEqD, smartConstructors]
         [''Val, ''Op, ''Abs, ''Var, ''Lam, ''App])


-- Nominal to PHOAS translation
type M f = Reader (Map.Map VarId (Term f))

class N2PTrans f g where
  n2pAlg :: Alg f (M g (Term g))

$(derive [liftSum] [''N2PTrans])

n2p :: (Difunctor f, N2PTrans f g) => Term f -> Term g
n2p x = runReader (cata n2pAlg x) Map.empty

instance (f :<: g, Ditraversable f (M g) Any) => N2PTrans f g where
  n2pAlg = liftM inject . disequence . dimap (return . P.Var) id -- default

instance (Lam :<: g) => N2PTrans Abs g where
  n2pAlg (Abs x b) = do
      vars <- ask
      return $ iLam x $ \y -> runReader b (Map.insert x y vars)

instance N2PTrans Var g where
  n2pAlg (Var x) = liftM fromJust (asks (Map.lookup x))

en :: Term SigN
en = iAbs "a" $ iAbs "b" (iAbs "a" $ iVar "b") `iApp` iVar "a"

ep :: Term SigP
ep = n2p en


-- PHOAS to nominal translation
class P2NTrans f g where
  p2nAlg :: Alg f (Term g)

$(derive [liftSum] [''P2NTrans])

p2n :: (Difunctor f, P2NTrans f g) => Term f -> Term g
p2n = cata p2nAlg

instance (Difunctor f, f :<: g) => P2NTrans f g where
  p2nAlg = inject . dimap P.Var id -- default

instance (Abs :<: g, Var :<: g) => P2NTrans Lam g where
  p2nAlg (Lam x f) = iAbs x (f $ iVar x)

ep' :: Term SigP
ep' = iLam "a" $ \a -> iLam "b" (\b -> (iLam "a" $ \a -> b)) `iApp` a

en' :: Term SigN
en' = p2n ep'