{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module DataTypes where

import Control.Monad.Fail


type Err = Either String

instance MonadFail Err where
    fail  = Left
