{-# LANGUAGE GADTs, TemplateHaskell #-}

module Data.ALaCarte.Multi.Example where

import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.HFunctor
import Data.ALaCarte.Multi.Algebra
import Data.ALaCarte.Derive
import Data.Typeable

isInt :: Typeable a => a -> Bool
isInt x = case cast x :: Maybe Int of
            Nothing -> False
            _ -> True

data Exp t where
    ELit :: t -> Exp t
    EAdd :: Exp Int -> Exp Int -> Exp Int
    EIf :: Exp Bool -> Exp t -> Exp t -> Exp t
    EGt :: Exp Int -> Exp Int -> Exp Bool
    EAnd :: Exp Bool -> Exp Bool -> Exp Bool
    ENeg :: Exp Bool -> Exp Bool
             

data Base e t where
    Lit :: t -> Base e t
    Add :: e Int -> e Int -> Base e Int
    If :: e Bool -> e t -> e t -> Base e t
    Gt :: e Int -> e Int -> Base e Bool
    And :: e Bool -> e Bool -> Base e Bool
    Neg :: e Bool -> Base e Bool
    List :: [e t] -> Base e [t]
    LList :: [[e t]] -> Base e [[t]]

$(derive [instanceHFunctor, instanceHFoldable, instanceHTraversable] [''Base])


evalAlg :: Alg Base I
evalAlg (Lit x) = I x
evalAlg (Add (I x) (I y)) = I (x + y)
evalAlg (If (I b) (I x) (I y)) = I $ if b then x else y

countAlg :: Alg Base (K Int)
countAlg (Lit _) = K 1
countAlg (Add (K x) (K y)) = K (x + y)
countAlg (If (K x) (K y) (K z)) = K (x + y + z)



eval :: Typeable t => Term Base t -> t
eval = unI . cata evalAlg

count :: Term Base Int -> Int
count = unK . cata countAlg