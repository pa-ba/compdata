{-# LANGUAGE TemplateHaskell, FlexibleContexts, MultiParamTypeClasses,
  TypeOperators, FlexibleInstances, UndecidableInstances,
  ScopedTypeVariables, TypeSynonymInstances #-}

module Examples.Automata.Compiler where

import Data.Comp.Automata
import Data.Comp.Zippable
import Data.Comp.Derive
import Data.Comp.Ops
import Data.Comp hiding (height)
import Data.Foldable
import Prelude hiding (foldl)

import Data.Set (Set, union, singleton, delete, member)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

type Var = String

data Val a = Const Int
data Op a  = Plus a a
           | Times a a
type Core = Op :+: Val
data Let a = Let Var a a
           | Var Var

type CoreLet = Let :+: Core

data Sugar a = Neg a
             | Minus a a

$(derive [makeFunctor, makeFoldable, smartConstructors, makeShowF] [''Val, ''Op, ''Let, ''Sugar])

instance Zippable Val where
    fzip _ (Const i) = Const i
instance Zippable Op where
    fzip (Cons a (Cons b _)) (Plus x y) = Plus (a,x) (b,y)
    fzip (Cons a (Cons b _)) (Times x y) = Times (a,x) (b,y)

instance Zippable Let where
    fzip (Cons a (Cons b _)) (Let v x y) = Let v (a,x) (b,y)
    fzip _ (Var v) = Var v
instance Zippable Sugar where
    fzip (Cons x _) (Neg y) = Neg (x,y)
    fzip (Cons a (Cons b _)) (Minus x y) = Minus (a,x) (b,y)

instance (Zippable f, Zippable g) => Zippable (f :+: g) where
    fzip x (Inl v) = Inl $ fzip x v
    fzip x (Inr v) = Inr $ fzip x v

class Eval f where
    evalSt :: UpState f Int

$(derive [liftSum] [''Eval])

instance Eval Val where
    evalSt (Const i) = i

instance Eval Op where
    evalSt (Plus x y) = x + y
    evalSt (Times x y) = x * y

type Addr = Int

data Instr = Acc Int
           | Load Addr
           | Store Addr
           | Add Int
           | Sub Int
           | Mul Int
             deriving (Show)

type Code = [Instr]

data MState = MState {
      mRam :: Map Addr Int,
      mAcc :: Int }

runCode :: Code -> MState -> MState
runCode [] = id
runCode (ins:c) = runCode c . step ins 
    where step (Acc i) s = s{mAcc = i}
          step (Load a) s = case Map.lookup a (mRam s) of
              Nothing -> error $ "memory cell " ++ show a ++ " is not set"
              Just n -> s {mAcc = n}
          step (Store a) s = s {mRam = Map.insert a (mAcc s) (mRam s)}
          step (Add a) s = exec (+) a s
          step (Sub a) s = exec (-) a s
          step (Mul a) s = exec (*) a s
          exec op a s = case Map.lookup a (mRam s) of
                        Nothing -> error $ "memory cell " ++ show a ++ " is not set"
                        Just n -> s {mAcc = mAcc s `op` n}


runCode' :: Code -> Int
runCode' c = mAcc $ runCode c MState{mRam = Map.empty, mAcc = error "accumulator is not set"}


-- | Defines the height of an expression.
heightSt' :: Foldable f => UpState f Int
heightSt' t = foldl max 0 t + 1

newtype Height = Height {height :: Int}
heightSt :: (Functor f,Foldable f) => UpState f Height
heightSt = tagUpState Height height heightSt'


-- | Defines the depth of a subexpression.
depthSt' :: Foldable f => DownState f Int
depthSt' (d,t) = Map.fromList [(s,d+1)| s <- toList t]

newtype Depth = Depth {depth :: Int}
depthSt :: (Foldable f) => DownState f Depth
depthSt = tagDownState Depth depth depthSt'


type Bind = Map Var Int

bindSt :: (Let :<: f,Depth :< q) => DDownState f q Bind
bindSt t = case proj t of
             Just (Let v _ e) -> Map.singleton e q'
                       where q' = Map.insert v (2 * depth above) above
             _ -> Map.empty


-- | Defines the code that an expression is compiled to. It depends on
-- an integer state that denotes the height of the current node.
class CodeSt f q where
    codeSt :: DUpState f q Code

$(derive [liftSum] [''CodeSt])

instance CodeSt Val q where
    codeSt (Const i) = [Acc i]

instance (Height :< q) => CodeSt Op q where
    codeSt (Plus x y) = below x ++ [Store i] ++ below y ++ [Add i]
        where i = 2*(height $ below y) +1
    codeSt (Times x y) = below x ++ [Store i] ++ below y ++ [Mul i]
        where i = 2*(height $ below y) +1

instance (Depth :< q, Bind :< q) => CodeSt Let q where
    codeSt (Let _ b e) = below b ++ [Store i] ++ below e
                    where i = 2 * depth above
    codeSt (Var v) = case Map.lookup v above of
                       Nothing -> error $ "unbound variable " ++ v
                       Just i -> [Load i]

compile' :: (CodeSt f (Code,Height), Foldable f, Functor f) => Term f -> Code
compile' = fst . runDUpState (codeSt `prodDUpState` dUpState heightSt)


exComp' = compile' (iConst 2 `iPlus` iConst 3 :: Term Core)



compile :: (CodeSt f ((Code,Height),(Bind,Depth)), Foldable f, Functor f, Let :<: f, Zippable f)
           => Term f -> Code
compile = fst . runDState 
          (codeSt `prodDUpState` dUpState heightSt)
          (bindSt `prodDDownState` dDownState depthSt)
          (Map.empty, Depth 0)
          

exComp = compile (iLet "x" (iLet "x" (iConst 5) (iConst 10 `iPlus` iVar "x")) (iConst 2 `iPlus` iVar "x") :: Term CoreLet)

-- | Defines the set of free variables
class VarsSt f where
    varsSt :: UpState f (Set Var)

$(derive [liftSum] [''VarsSt])

instance VarsSt Val where
    varsSt _ = Set.empty

instance VarsSt Op where
    varsSt (Plus x y) = x `union` y
    varsSt (Times x y) = x `union` y

instance VarsSt Let where
    varsSt (Var v) = singleton v
    varsSt (Let v x y) = (if v `member` y then x else Set.empty) `union` (delete v y)

-- | Stateful homomorphism that removes unnecessary let bindings.
remLetHom :: (Set Var :< q, Let :<: f, Functor f) => QHom f q f
remLetHom t = case proj t of
                Just (Let v _ y) 
                    | not (v `member` below y) -> Hole y
                _ -> simpCxt t

-- | Removes unnecessary let bindings.
remLet :: (Let :<: f, Functor f, VarsSt f) => Term f -> Term f
remLet = runUpHom varsSt remLetHom

exLet = remLet (iLet "x" (iConst 3) (iConst 2 `iPlus` iVar "y") :: Term CoreLet)
