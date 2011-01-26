{-# LANGUAGE GADTs, TemplateHaskell, FlexibleContexts, TypeFamilies,
  TypeOperators, ScopedTypeVariables, RankNTypes, FlexibleInstances #-}

module Data.ALaCarte.Multi.Example where

import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.HFunctor
import Data.ALaCarte.Multi.Algebra
import Data.ALaCarte.Multi.Sum
import Data.ALaCarte.Derive

import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Map (Map)

type Var = String

data Exp t where
    ELit :: t -> Exp t
    EAdd :: Exp Int -> Exp Int -> Exp Int
    EIf :: Exp Bool -> Exp t -> Exp t -> Exp t
    EGt :: Exp Int -> Exp Int -> Exp Bool
    EAnd :: Exp Bool -> Exp Bool -> Exp Bool
    ENot :: Exp Bool -> Exp Bool
             

class BoolInt e where
    toBI :: e -> Either Bool Int
    isBool :: e -> Bool
    isBool e = case toBI e of
                 Left _ -> True
                 _ -> False
    isInt :: e -> Bool
    isInt e = case toBI e of
                 Right _ -> True
                 _ -> False

instance BoolInt Int where
    toBI = Right

instance BoolInt Bool where
    toBI = Left

instance BoolInt (Either Bool Int) where
    toBI = id

data Base e t where
    Lit :: BoolInt t => t -> Base e t
    Add :: e Int -> e Int -> Base e Int
    If :: BoolInt t => e Bool -> e t -> e t -> Base e t
    Gt :: e Int -> e Int -> Base e Bool
    And :: e Bool -> e Bool -> Base e Bool
    Not :: e Bool -> Base e Bool

type Env = Map Var (Either Bool Int)
data StmtL = StmtL Env

data Let e t where
    Let :: BoolInt t => e StmtL -> e t -> Let e t
    Var :: Var -> Let e (Either Bool Int)

data Stmt e t where
    Seq :: e StmtL -> e StmtL -> Stmt e StmtL
    Bind :: BoolInt t => Var -> e t -> Stmt e StmtL

$(derive [instanceHFunctor, instanceHFoldable, instanceHTraversable] [''Base])



count :: (Base :<<: f, HFoldable f) => Term f Int -> Int
count = unK . cata countAlg

countAlg :: (Base :<<: f, HFoldable f) => Alg f (K Int)
countAlg v = case hproj v of
               Just (Lit e) -> if isInt e then K 1 else K 0
               _ -> K $ kfoldl (+) 0 v


sevalAlg :: Alg Base I
sevalAlg (Lit x) = I x
sevalAlg (Add (I x) (I y)) = I (x + y)
sevalAlg (If (I b) (I x) (I y)) = I $ if b then x else y
sevalAlg (Gt (I x) (I y)) = I (x > y)
sevalAlg (And (I x) (I y)) = I (x && y)
sevalAlg (Not (I x)) = I (not x)


seval :: Term Base i -> i
seval = unI . cata sevalAlg

type EvalM = Reader Env


class Eval f where
    evalAlg :: Alg f EvalM

eval :: (Eval f,HFunctor f) => Term f t -> t
eval = (`runReader` Map.empty) . cata evalAlg

instance (Eval f, Eval g) => Eval (f :++: g) where
    evalAlg (HInl v) = evalAlg v
    evalAlg (HInr v) = evalAlg v

instance Eval Base where
    evalAlg = liftMAlg sevalAlg


instance Eval Let where
    evalAlg (Let s e) = do StmtL env <- s
                           local (Map.union env) e
    evalAlg (Var v) = do env <- ask
                         case Map.lookup v env of
                           Nothing -> fail "open expression"
                           Just x -> return x

instance Eval Stmt where
    evalAlg (Seq x y) = do StmtL e1 <- x
                           StmtL e2 <- y
                           return $ StmtL (e1 `Map.union` e2)
    evalAlg (Bind v x) = liftM (StmtL . Map.singleton v . toBI) x