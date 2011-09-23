{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.Injections
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Derive functions for signature injections.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.Injections
    (
     injn,
     injectn,
     deepInjectn
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Term
import Data.Comp.Algebra (CxtFun, appSigFun)
import Data.Comp.Ops ((:+:)(..), (:<:)(..))

injn :: Int -> Q [Dec]
injn n = do
  let i = mkName $ "inj" ++ show n
  let fvars = map (\n -> mkName $ 'f' : show n) [1..n]
  let gvar = mkName "g"
  let avar = mkName "a"
  let xvar = mkName "x"
  let d = [funD i [clause [varP xvar] (normalB $ genDecl xvar n) []]]
  sequence $ sigD i (genSig fvars gvar avar) : d
    where genSig fvars gvar avar = do
            let cxt = map (\f -> classP ''(:<:) [varT f, varT gvar]) fvars
            let tp = foldl1 (\a f -> conT ''(:+:) `appT` f `appT` a)
                            (map varT fvars)
            let tp' = arrowT `appT` (tp `appT` varT avar)
                             `appT` (varT gvar `appT` varT avar)
            forallT (map PlainTV $ gvar : avar : fvars)
                    (sequence cxt) tp'
          genDecl x n = [| case $(varE x) of
                             Inl x -> $(varE $ mkName "inj") x
                             Inr x -> $(varE $ mkName $ "inj" ++
                                        if n > 2 then show (n - 1) else "") x |]
injectn :: Int -> Q [Dec]
injectn n = do
  let i = mkName ("inject" ++ show n)
  let fvars = map (\n -> mkName $ 'f' : show n) [1..n]
  let gvar = mkName "g"
  let avar = mkName "a"
  let d = [funD i [clause [] (normalB $ genDecl n) []]]
  sequence $ sigD i (genSig fvars gvar avar) : d
    where genSig fvars gvar avar = do
            let hvar = mkName "h"
            let cxt = map (\f -> classP ''(:<:) [varT f, varT gvar]) fvars
            let tp = foldl1 (\a f -> conT ''(:+:) `appT` f `appT` a)
                            (map varT fvars)
            let tp' = conT ''Cxt `appT` varT hvar `appT` varT gvar
                                 `appT` varT avar
            let tp'' = arrowT `appT` (tp `appT` tp') `appT` tp'
            forallT (map PlainTV $ hvar : gvar : avar : fvars)
                    (sequence cxt) tp''
          genDecl n = [| Term . $(varE $ mkName $ "inj" ++ show n) |]

deepInjectn :: Int -> Q [Dec]
deepInjectn n = do
  let i = mkName ("deepInject" ++ show n)
  let fvars = map (\n -> mkName $ 'f' : show n) [1..n]
  let gvar = mkName "g"
  let d = [funD i [clause [] (normalB $ genDecl n) []]]
  sequence $ sigD i (genSig fvars gvar) : d
    where genSig fvars gvar = do
            let cxt = map (\f -> classP ''(:<:) [varT f, varT gvar]) fvars
            let tp = foldl1 (\a f -> conT ''(:+:) `appT` f `appT` a)
                            (map varT fvars)
            let cxt' = classP ''Functor [tp]
            let tp' = conT ''CxtFun `appT` tp `appT` varT gvar
            forallT (map PlainTV $ gvar : fvars) (sequence $ cxt' : cxt) tp'
          genDecl n = [| appSigFun $(varE $ mkName $ "inj" ++ show n) |]