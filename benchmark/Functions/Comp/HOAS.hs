{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances #-}

module Functions.Comp.Desugar where

import DataTypes.Comp
import Data.Comp.ExpFunctor
import Data.Comp
import Data.Foldable
import Prelude hiding (foldr)

ex1 :: HOASExpr
ex1 = iLam (\x -> case project x of
                    Just (VInt _) -> x 
                    _ -> x `iPlus` x)
ex2 :: HOASExpr
ex2 = iLam (\x -> case x of
                    Term t -> case proj t of
                                Just (VInt _) -> x 
                                _ -> x `iPlus` x)
                                

class Vars f where
    varsAlg :: Alg f Int

instance (Vars f, Vars g) => Vars (g :+: f) where
    varsAlg (Inl v) = varsAlg v
    varsAlg (Inr v) = varsAlg v

instance Vars Lam where
    varsAlg (Lam f) = f 1

instance Vars App where
    varsAlg = foldr (+) 0

instance Vars Value where
    varsAlg = foldr (+) 0

instance Vars Op where
    varsAlg = foldr (+) 0


instance Vars Sugar where
    varsAlg = foldr (+) 0

vars :: (ExpFunctor f, Vars f) => Term f -> Int
vars = cataE varsAlg