{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP #-}

module DataTypes where

-- Control.Monad.Fail import is redundant since GHC 8.8.1
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail
#endif


type Err = Either String

instance MonadFail Err where
    fail  = Left
