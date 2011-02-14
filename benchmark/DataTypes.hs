{-# LANGUAGE TypeSynonymInstances, CPP #-}

module DataTypes where

type Err = Either String

#if __GLASGOW_HASKELL__ < 700
instance Monad Err where
    return = Right
    e >>= f = case e of 
                Left m -> Left m
                Right x -> f x
    fail  = Left
#endif