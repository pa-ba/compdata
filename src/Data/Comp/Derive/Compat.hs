{-# LANGUAGE FlexibleInstances #-}

-- | Compatibility with different versions of GHC

module Data.Comp.Derive.Compat
    (
      conP_
    , doE_
    )
where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

class C a where
    c :: a -> Name -> [Pat] -> Pat
instance C (Name -> [Pat] -> Pat) where
    c x = x
instance C (Name -> [Type] -> [Pat] -> Pat) where
    c x n = x n []
conP_ = c ConP

class D a where
    d :: a -> [Stmt] -> Exp
instance D ([Stmt] -> Exp) where
    d x = x
instance D (Maybe ModName -> [Stmt] -> Exp) where
    d x = x Nothing
doE_ = d DoE
