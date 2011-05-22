{-# LANGUAGE TemplateHaskell, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Projections
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Derive functions for signature projections.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.Projections
    (
     projn,
     projectn,
     deepProjectn
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Control.Monad (liftM)
import Data.Traversable (Traversable)
import Data.Comp.Term
import Data.Comp.Algebra (appSigFunM')
import Data.Comp.Ops ((:+:)(..), (:<:)(..))

projn :: Int -> Q [Dec]
projn n = do
  let p = mkName $ "proj" ++ show n
  gvars <- newNames n "g"
  avar <- newName "a"
  xvar <- newName "x"
  let d = [funD p [clause [varP xvar] (normalB $ genDecl xvar gvars avar) []]]
  sequence $ (sigD p $ genSig gvars avar) : d
    where genSig gvars avar = do
            fvar <- newName "f"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp' = foldl1 (\a g -> appT (appT (conT ''(:+:)) g) a)
                             (map varT gvars)
            let tp = appT (appT arrowT (appT (varT fvar) (varT avar)))
                          (appT (conT $ mkName "Maybe") (appT tp' (varT avar)))
            forallT (map PlainTV $ fvar : avar : gvars) (sequence cxt) tp
          genDecl x [g] a = [| liftM inj (proj $(varE x)
                                          :: Maybe ($(varT g) $(varT a))) |]
          genDecl x (g:gs) a = [| case (proj $(varE x)
                                            :: Maybe ($(varT g) $(varT a))) of
                                     Just y -> Just $ inj y
                                     _ -> $(genDecl x gs a)|]
          genDecl _ _ _ = error "genDecl called with empty list"

projectn :: Int -> Q [Dec]
projectn n = do
  let p = mkName ("project" ++ show n)
  gvars <- newNames n "g"
  avar <- newName "a"
  xvar <- newName "x"
  let d = [funD p [clause [varP xvar] (normalB $ genDecl xvar n) []]]
  sequence $ (sigD p $ genSig gvars avar) : d
    where genSig gvars avar = do
            fvar <- newName "f"
            hvar <- newName "h"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp' = foldl1 (\a g -> appT (appT (conT ''(:+:)) g) a)
                             (map varT gvars)
            let tp'' = appT (appT (appT (conT $ mkName "Cxt") (varT hvar))
                                  (varT fvar)) (varT avar)
            let tp = appT (appT arrowT tp'')
                          (appT (conT $ mkName "Maybe") (appT tp' tp''))
            forallT (map PlainTV $ hvar : fvar : avar : gvars) (sequence cxt) tp
          genDecl x n = [| case $(varE x) of
                             Hole _ -> Nothing
                             Term t -> $(varE $ mkName $ "proj" ++ show n) t |]


deepProjectn :: Int -> Q [Dec]
deepProjectn n = do
  let p = mkName ("deepProject" ++ show n)
  gvars <- newNames n "g"
  avar <- newName "a"
  let d = [funD p [clause [] (normalB $ genDecl n) []]]
  sequence $ (sigD p $ genSig gvars avar) : d
    where genSig gvars avar = do
            fvar <- newName "f"
            hvar <- newName "h"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let cxt' = map (\g -> classP ''Traversable [varT g]) gvars
            let tp' = foldl1 (\a g -> appT (appT (conT ''(:+:)) g) a)
                             (map varT gvars)
            let tp'' = appT (appT (appT (conT $ mkName "Cxt") (varT hvar))
                                  (varT fvar)) (varT avar)
            let tp''' = appT (appT (appT (conT $ mkName "Cxt") (varT hvar)) tp')
                             (varT avar)
            let tp = appT (appT arrowT tp'')
                          (appT (conT $ mkName "Maybe") tp''')
            forallT (map PlainTV $ hvar : fvar : avar : gvars)
                    (sequence $ cxt ++ cxt') tp
          genDecl n = [| appSigFunM' $(varE $ mkName $ "proj" ++ show n) |]