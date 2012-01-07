{-# LANGUAGE TemplateHaskell, FlexibleContexts, MultiParamTypeClasses,
TypeOperators, FlexibleInstances, UndecidableInstances,
ScopedTypeVariables, TypeSynonymInstances, GeneralizedNewtypeDeriving,
OverlappingInstances #-}

module Examples.Automata.Compiler where

import Data.Comp.Automata
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

$(derive [makeFunctor, makeFoldable, makeTraversable, smartConstructors, makeShowF]
  [''Val, ''Op, ''Let, ''Sugar])


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
heightSt :: Foldable f => UpState f Int
heightSt t = foldl max 0 t + 1

tmpAddrSt :: Foldable f => UpState f Int
tmpAddrSt = (+1) . heightSt


newtype VarAddr = VarAddr {varAddr :: Int} deriving (Eq, Show, Num)

class VarAddrSt f where
  varAddrSt :: DownState f VarAddr
  
instance (VarAddrSt f, VarAddrSt g) => VarAddrSt (f :+: g) where
    varAddrSt (q,Inl x) = varAddrSt (q, x)
    varAddrSt (q,Inr x) = varAddrSt (q, x)

instance VarAddrSt Let where
  varAddrSt (d, Let _ _ x) = x `Map.singleton` (d + 2)
  varAddrSt _ = Map.empty
  
instance VarAddrSt f where
  varAddrSt _ = Map.empty


type Bind = Map Var Int

bindSt :: (Let :<: f,VarAddr :< q) => DDownState f q Bind
bindSt t = case proj t of
             Just (Let v _ e) -> Map.singleton e q'
                       where q' = Map.insert v (varAddr above) above
             _ -> Map.empty

-- | Defines the code that an expression is compiled to. It depends on
-- an integer state that denotes the height of the current node.
class CodeSt f q where
    codeSt :: DUpState f q Code

instance (CodeSt f q, CodeSt g q) => CodeSt (f :+: g) q where
    codeSt (Inl x) = codeSt x
    codeSt (Inr x) = codeSt x
  

instance CodeSt Val q where
    codeSt (Const i) = [Acc i]

instance (Int :< q) => CodeSt Op q where
    codeSt (Plus x y) = below x ++ [Store i] ++ below y ++ [Add i]
        where i = below y
    codeSt (Times x y) = below x ++ [Store i] ++ below y ++ [Mul i]
        where i = below y

instance (VarAddr :< q, Bind :< q) => CodeSt Let q where
    codeSt (Let _ b e) = below b ++ [Store i] ++ below e
                    where i = varAddr above
    codeSt (Var v) = case Map.lookup v above of
                       Nothing -> error $ "unbound variable " ++ v
                       Just i -> [Load i]

compile' :: (CodeSt f (Code,Int), Foldable f, Functor f) => Term f -> Code
compile' = fst . runDUpState (codeSt `prodDUpState` dUpState tmpAddrSt)


exComp' = compile' (iConst 2 `iPlus` iConst 3 :: Term Core)



compile :: (CodeSt f ((Code,Int),(Bind,VarAddr)), Traversable f, Functor f, Let :<: f, VarAddrSt f)
           => Term f -> Code
compile = fst . runDState 
          (codeSt `prodDUpState` dUpState tmpAddrSt)
          (bindSt `prodDDownState` dDownState varAddrSt)
          (Map.empty, VarAddr 1)
          

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
    varsSt (Let v x y) = (if v `member` y then x else Set.empty) `union` delete v y

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
