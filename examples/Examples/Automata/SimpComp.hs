{-# LANGUAGE TemplateHaskell, FlexibleContexts, MultiParamTypeClasses,
  TypeOperators, FlexibleInstances, UndecidableInstances,
  ScopedTypeVariables, TypeSynonymInstances, RankNTypes #-}

module Examples.Automata.Compiler where


import Data.Comp.Automata hiding (DUpState, (<*>), runDUpState, dUpState)
import Data.Comp.Zippable
import Data.Comp.Derive
import Data.Comp.Ops
import Data.Comp hiding (height)
import Prelude hiding (foldl)



type Var = String

data Sig a = Const Int | Plus a a
data Let a = Let Var a a
           | Var Var


$(derive [makeFunctor, makeFoldable, smartConstructors, makeShowF] [''Sig, ''Let])

instance Zippable Sig where
    fzip _ (Const i) = Const i
    fzip (Cons a (Cons b _)) (Plus x y) = Plus (a,x) (b,y)

instance Zippable Let where
    fzip (Cons a (Cons b _)) (Let v x y) = Let v (a,x) (b,y)
    fzip _ (Var v) = Var v


instance (Zippable f, Zippable g) => Zippable (f :+: g) where
    fzip x (Inl v) = Inl $ fzip x v
    fzip x (Inr v) = Inr $ fzip x v

evalSt :: UpState Sig Int
evalSt (Const i) = i
evalSt (Plus x y) = x + y

type Addr = Int

data Instr = Acc Int
           | Load Addr
           | Store Addr
           | Add Addr
             deriving (Show)

type Code = [Instr]



type DUpState f q p = (q :< p) => f p -> q

dUpState :: Functor f => UpState f q -> DUpState f q p
dUpState st = st . fmap pr


heightSt :: UpState Sig Int
heightSt (Const _) = 0
heightSt (Plus x y) = 1 + max x y

codeSt :: (Int :< q) => DUpState Sig Code q
codeSt (Const x) = [Acc x]
codeSt (Plus x y) = pr x ++ [Store a] ++ pr y ++ [Add a] where a = pr y

-- | This combinator constructs the product of two GDUTA.
(<*>) :: (p :< pq, q :< pq)
             => DUpState f p pq -> DUpState f q pq -> DUpState f (p,q) pq
(sp <*> sq) t = (sp t, sq t)
    
runDUpState :: Functor f => DUpState f q q -> Term f -> q
runDUpState f = cata f

code :: Term Sig -> Code
code = fst . runDUpState (codeSt <*> dUpState heightSt)
 