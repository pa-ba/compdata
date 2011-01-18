{-# LANGUAGE TypeSynonymInstances #-}

module DataTypes where

type Err = Either String

instance Monad Err where
    return = Right
    e >>= f = case e of 
                Left m -> Left m
                Right x -> f x
    fail  = Left