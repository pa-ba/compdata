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
import Control.Monad (liftM)
import Data.Traversable (Traversable)
import Data.Comp.Term
import Data.Comp.Algebra (CxtFunM, appSigFunM')
import Data.Comp.Ops ((:+:)(..), (:<:), proj, inj)

projn :: Int -> Q [Dec]
projn n = do
  let p = mkName $ "proj" ++ show n
  let gvars = map (\n -> mkName $ 'g' : show n) [1..n]
  let avar = mkName "a"
  let xvar = mkName "x"
  let d = [funD p [clause [varP xvar] (normalB $ genDecl xvar gvars avar) []]]
  sequence $ (sigD p $ genSig gvars avar) : d
    where genSig gvars avar = do
            let fvar = mkName "f"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp = foldl1 (\a g -> conT ''(:+:) `appT` g `appT` a)
                            (map varT gvars)
            let tp' = arrowT `appT` (varT fvar `appT` varT avar)
                             `appT` (conT ''Maybe `appT`
                                     (tp `appT` varT avar))
            forallT (map PlainTV $ fvar : avar : gvars) (sequence cxt) tp'
          genDecl x [g] a =
            [| liftM inj (proj $(varE x)
                          :: Maybe ($(varT g `appT` varT a))) |]
          genDecl x (g:gs) a =
            [| case (proj $(varE x)
                         :: Maybe ($(varT g `appT` varT a))) of
                 Just y -> Just $ inj y
                 _ -> $(genDecl x gs a) |]
          genDecl _ _ _ = error "genDecl called with empty list"

projectn :: Int -> Q [Dec]
projectn n = do
  let p = mkName ("project" ++ show n)
  let gvars = map (\n -> mkName $ 'g' : show n) [1..n]
  let avar = mkName "a"
  let xvar = mkName "x"
  let d = [funD p [clause [varP xvar] (normalB $ genDecl xvar n) []]]
  sequence $ (sigD p $ genSig gvars avar) : d
    where genSig gvars avar = do
            let fvar = mkName "f"
            let hvar = mkName "h"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp = foldl1 (\a g -> conT ''(:+:) `appT` g `appT` a)
                            (map varT gvars)
            let tp' = conT ''Cxt `appT` varT hvar `appT` varT fvar
                                 `appT` varT avar
            let tp'' = arrowT `appT` tp'
                              `appT` (conT ''Maybe `appT` (tp `appT` tp'))
            forallT (map PlainTV $ hvar : fvar : avar : gvars)
                    (sequence cxt) tp''
          genDecl x n = [| case $(varE x) of
                             Hole _ -> Nothing
                             Term t -> $(varE $ mkName $ "proj" ++ show n) t |]

deepProjectn :: Int -> Q [Dec]
deepProjectn n = do
  let p = mkName ("deepProject" ++ show n)
  let gvars = map (\n -> mkName $ 'g' : show n) [1..n]
  let d = [funD p [clause [] (normalB $ genDecl n) []]]
  sequence $ (sigD p $ genSig gvars) : d
    where genSig gvars = do
            let fvar = mkName "f"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp = foldl1 (\a g -> conT ''(:+:) `appT` g `appT` a)
                            (map varT gvars)
            let cxt' = classP ''Traversable [tp]
            let tp' = conT ''CxtFunM `appT` conT ''Maybe
                                     `appT` varT fvar `appT` tp
            forallT (map PlainTV $ fvar : gvars) (sequence $ cxt' : cxt) tp'
          genDecl n = [| appSigFunM' $(varE $ mkName $ "proj" ++ show n) |]
