{-# LANGUAGE GADTs #-}

module Data.ALaCarte.Multi.Example where

import Data.ALaCarte.Multi.Term
import Data.ALaCarte.Multi.HFunctor
import Data.ALaCarte.Multi.Algebra
import Data.Typeable

import Control.Monad

isInt :: Typeable a => a -> Bool
isInt x = case cast x :: Maybe Int of
            Nothing -> False
            _ -> True

data SigInt = ILit Int
            | IAdd SigInt SigInt
            | IIf SigBool SigInt SigInt

data SigBool = BGt SigInt SigInt
             

data Sig e t where
    Lit :: t -> Sig e t
    Add :: e Int -> e Int -> Sig e Int
    If :: e Bool -> e t -> e t -> Sig e t

instance HFunctor Sig where
    hfmap _ (Lit x) = Lit x
    hfmap f (Add x y) = Add (f x) (f y)
    hfmap f (If x y z) = If (f x) (f y) (f z)

instance HFoldable Sig where
    hfoldr _ e (Lit _) = e
    hfoldr f e (Add x y) = x `f` (y `f` e)
    hfoldr f e (If x y z) = x `f` (y `f` (z `f` e))

    hfoldl _ e (Lit _) = e
    hfoldl f e (Add x y) = (e `f` x) `f` y
    hfoldl f e (If x y z) = ((e `f` x) `f` y) `f` z

instance HTraversable Sig where
    hmapM _ (Lit x) = return $ Lit x
    hmapM f (Add x y) = liftM2 Add (f x) (f y)
    hmapM f (If x y z) = liftM3 If (f x) (f y) (f z)


evalAlg :: Alg Sig I
evalAlg (Lit x) = I x
evalAlg (Add (I x) (I y)) = I (x + y)
evalAlg (If (I b) (I x) (I y)) = I $ if b then x else y

countAlg :: Alg Sig (K Int)
countAlg (Lit x)
    | isInt x = K 1
    | otherwise = K 0

countAlg (Add (K x) (K y)) = K (x + y)
countAlg (If (K x) (K y) (K z)) = K (x + y + z)



eval :: Typeable t => Term Sig t -> t
eval = unI . cata evalAlg

count :: Term Sig Int -> Int
count = unK . cata countAlg