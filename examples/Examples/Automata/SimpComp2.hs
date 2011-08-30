{-# LANGUAGE TemplateHaskell, FlexibleContexts, MultiParamTypeClasses,
  TypeOperators, FlexibleInstances, UndecidableInstances,
  ScopedTypeVariables, TypeSynonymInstances, RankNTypes, ImplicitParams, DeriveDataTypeable #-}

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

data Sig e = Const Int | Plus e e | LetIn Var e e | Var Var


$(derive [makeFunctor, makeFoldable, smartConstructors, makeShowF] [''Sig])

instance Zippable Sig where
    fzip _ (Const i) = Const i
    fzip (Cons a (Cons b _)) (Plus x y) = Plus (a,x) (b,y)
    fzip (Cons a (Cons b _)) (LetIn v x y) = LetIn v (a,x) (b,y)
    fzip _ (Var v) = Var v


instance (Zippable f, Zippable g) => Zippable (f :+: g) where
    fzip x (Inl v) = Inl $ fzip x v
    fzip x (Inr v) = Inr $ fzip x v

-- evalSt :: UpState Sig Int
-- evalSt (Const i) = i
-- evalSt (Plus x y) = x + y

type Addr = Int

data Instr = Acc Int
           | Load Addr
           | Store Addr
           | Add Addr
             deriving (Show)

type Code = [Instr]



-- heightSt :: UpState Sig Int
-- heightSt (Const _) = 0
-- heightSt (Plus x y) = 1 + max x y
-- heightSt (LetIn _ e b) = 1 + max e b
-- heightSt (Var _) = 0

-- codeSt :: (Int :< q) => DUpState Sig q Code 
-- codeSt (Const x) = [Acc x]
-- codeSt (Plus x y) = below x ++ [Store a] ++ below y ++ [Add a] where a = below y


-- code :: Term Sig -> Code
-- code = fst . runDUpState (codeSt <*> dUpState heightSt)


type Vars = Set Var

fvSt :: UpState Sig Vars
fvSt (Var v)  = singleton v
fvSt (LetIn v e b)  | v `member` b  = e `union` delete v b
                    | otherwise     =  delete v b
fvSt t        = foldl union Set.empty t

-- | Stateful homomorphism that removes unnecessary let bindings.
remLetHom :: (Vars :< q) => QHom Sig q Sig
remLetHom (LetIn v _ y) | not (v `Set.member` below y) = Hole y
remLetHom  t = simpCxt t

remLet :: Term Sig -> Term Sig
remLet = snd . runUpHom fvSt remLetHom

ldepthSt :: DownState Sig Int
ldepthSt (d,LetIn _ _ b) = b |-> d + 1
ldepthSt _               = o

type Ren = Map Var Var


newVar :: (?above :: q, Int :< q) => Var
newVar = show (above :: Int)

renSt :: (Int :< q) => DDownState Sig q Ren
renSt (LetIn v _ b) = b |-> (v |-> newVar & above)
renSt _             = o

renameHom :: (Ren :< q, Int :< q) => QHom Sig q Sig
renameHom (LetIn _ a b) = iLetIn newVar (Hole a) (Hole b)
renameHom (Var v) = case Map.lookup v above of
                      Nothing -> iVar v
                      Just v' -> iVar v'
renameHom t = simpCxt t

renameInit :: (Ren, Int)
renameInit = (o, 0)

rename :: Term Sig -> Term Sig
rename = runDownHom (downState (renSt >*< dDownState ldepthSt))
         renameHom renameInit


heightSt :: Foldable f => UpState f Int
heightSt t = foldl max 0 t + 1

newtype Height = Height {height :: Int}

heightSt' :: (Functor f,Foldable f) => UpState f Height
heightSt' = tagUpState Height height heightSt


newtype Depth = Depth {depth :: Int}

ldepthSt' :: DownState Sig Depth
ldepthSt' = tagDownState Depth depth ldepthSt

type Bind = Map Var Int

bindSt :: (Depth :< q) => DDownState Sig q Bind 
bindSt (LetIn v _ e)  = e |-> (v |-> 2 * depth above & above)
bindSt _              = o

codeSt :: (Height :< q, Depth :< q, Bind :< q) => DUpState Sig q Code 
codeSt (Const x) = [Acc x]
codeSt (Plus x y) = below x ++ [Store a] ++ below y ++ [Add a] 
    where a = 2 * height (below y) + 1
codeSt (LetIn _ b e) = below b ++ [Store a] ++ below e
    where a = 2 * depth above
codeSt (Var v) = case Map.lookup v above of
                       Nothing -> error $ "unbound variable " ++ v
                       Just i -> [Load i]


code :: Term Sig -> (Code, Height)
code = runDState 
          (codeSt <*> dUpState heightSt')
          (bindSt >*< dDownState ldepthSt')
          (o :: Bind, Depth 0)