{-# LANGUAGE TemplateHaskell, TypeSynonymInstances,
FlexibleInstances, MultiParamTypeClasses, TypeOperators, FlexibleContexts#-}

module Data.Comp.Variables_Test where


import Data.Comp.Variables
import Data.Comp.Derive
import Data.Comp.Sum
import Data.Comp.Term

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck



--------------------------------------------------------------------------------
-- Definitions
--------------------------------------------------------------------------------

data Var = X | Y | Z deriving (Eq,Ord,Show)


data Val e = Abs Var e
           | Var Var
           | Int Int

data Op e = App e e
          | Plus e e

data Let e = Let Var e e

data LetRec e = LetRec Var e e

type Sig = Op :+: Val

type SigLet = Let :+: Sig

type SigRec = LetRec :+: Sig

$(derive [makeFunctor, makeTraversable, makeFoldable,
          makeEqF, makeShowF, smartConstructors]
         [''Op, ''Val, ''Let, ''LetRec])

instance HasVars Val Var where
    isVar (Var v) = Just v
    isVar _       = Nothing
    
    bindsVars (Abs v a) = Map.singleton a (Set.singleton v)
    bindsVars _         = Map.empty

instance HasVars Op a where

instance HasVars Let Var where
    bindsVars (Let v _ a) = Map.singleton a (Set.singleton v)

instance HasVars LetRec Var where
    bindsVars (LetRec v a b) = Map.fromList [(a,vs),(b,vs)]
        where vs = Set.singleton v

-- let x = x + 1 in (\y. y + x) z
letExp, letExp' :: Term SigLet
letExp = iLet X (iVar X `iPlus` iInt 1) (iAbs Y (iVar Y `iPlus` iVar X) `iApp` iVar Z)
letExp' = iLet X (iInt 1 `iPlus` iInt 1) (iAbs Y (iVar Y `iPlus` iVar X) `iApp` iInt 3)

-- letrec x = x + 1 in (\y. y + x) z
recExp, recExp :: Term SigRec
recExp = iLetRec X (iVar X `iPlus` iInt 1) (iAbs Y (iVar Y `iPlus` iVar X) `iApp` iVar Z)
recExp' = iLetRec X (iVar X `iPlus` iInt 1) (iAbs Y (iVar Y `iPlus` iVar X) `iApp` iInt 3)

subst :: (Val :<: f) => Subst f Var
subst = Map.fromList [(X, iInt 1), (Y, iInt 2), (Z, iInt 3)]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_letFree = variables letExp == Set.fromList [Z,X]

prop_recFree = variables recExp == Set.fromList [Z]

prop_letSubst = appSubst s letExp == letExp'
    where s = subst :: Subst SigLet Var

prop_recSubst = appSubst s recExp == recExp'
    where s = subst :: Subst SigRec Var

--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "Variables" [
         testProperty "prop_letFree" prop_letFree
        ,testProperty "prop_recFree" prop_recFree
        ]