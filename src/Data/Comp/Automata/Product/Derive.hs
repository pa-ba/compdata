{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Automata.Product.Derive
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.Automata.Product.Derive where

import Language.Haskell.TH

-- | An instance @a :< b@ means that @a@ is a component of @b@. @a@
-- can be extracted from @b@ via the method 'pr'.
class a :< b where
    pr :: b -> a

data Dir = L | R
         deriving Show

genAllInsts :: Int -> Q [Dec]
genAllInsts n = mapM genInst dirs
    where dirs = map (L:) (genDirs n)

genDirs :: Int -> [[Dir]]
genDirs 0 = [[]]
genDirs n = [] : map (L:) dirs ++ map (R:) dirs
    where dirs = genDirs (n-1)

genInst :: [Dir] -> Q Dec
genInst dir = do
  n <- newName "a"
  ty <- genType n dir
  ex <- genEx dir
  return $ InstanceD [] (ConT (mkName ":<") `AppT` VarT n `AppT` ty) [ex]

genType :: Name -> [Dir] -> Q Type
genType n = gen
    where gen [] = varT n
          gen (L:dir) =  gen dir `pairT` (varT =<< newName "a")
          gen (R:dir) =  (varT =<< newName "a") `pairT` gen dir

genPat :: Name -> [Dir] -> PatQ
genPat n = gen where
    gen [] = varP n
    gen (L:dir) = tupP [gen dir,wildP]
    gen (R:dir) = tupP [wildP,gen dir]

genEx :: [Dir] -> DecQ
genEx dir = do
  n <- newName "x"
  p <- genPat n dir
  return $ FunD (mkName "pr") [Clause [p] (NormalB (VarE n)) []]

genPatExp :: Name -> [Dir] -> Q (Pat, Exp)
genPatExp n = gen where
    gen [] = return (WildP, VarE n)
    gen (d:dir) = do
      (p,e) <- gen dir
      x <- newName "x"
      return $ case d of
        L -> (TupP [p,VarP x] , TupE [e,VarE x])
        R -> (TupP [VarP x,p] , TupE [VarE x,e])



pairT :: TypeQ -> TypeQ -> TypeQ
pairT x = appT (appT (tupleT 2) x)
