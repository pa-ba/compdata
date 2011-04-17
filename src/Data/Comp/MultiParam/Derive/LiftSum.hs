{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for difunctors to sums of difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Derive.LiftSum
    (
     liftSum,
     caseD
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.MultiParam.Sum
import Data.Comp.MultiParam.Ops ((:+:)(..))

{-| Given the name of a type class, where the first parameter is a difunctor,
  lift it to sums of difunctors. Example: @class ShowD f where ...@ is lifted
  as @instance (ShowD f, ShowD g) => ShowD (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum fname = do
  ClassI (ClassD _ name targs _ decs) _ <- abstractNewtypeQ $ reify fname
  targs' <- newNames (length targs - 1) "x"
  f <- newName "f"
  g <- newName "g"
  let cxt = [ClassP name (map VarT $ f : targs'),
             ClassP name (map VarT $ g : targs')]
  let tp = ConT name `AppT` ((ConT ''(:+:) `AppT` VarT f) `AppT` VarT g)
  let complType = foldl (\a x -> a `AppT` (VarT x)) tp targs'
  decs' <- sequence $ concatMap decl decs
  return [InstanceD cxt complType decs']
      where decl :: Dec -> [DecQ]
            decl (SigD f _) = [funD f [clause f]]
            decl _ = []
            clause :: Name -> ClauseQ
            clause f = do x <- newName "x"
                          b <- normalB [|caseD $(varE f) $(varE f) $(varE x)|]
                          return $ Clause [VarP x] b []

{-| Utility function to case on a difunctor sum, without exposing the internal
  representation of sums. -}
caseD :: (f a b i -> c) -> (g a b i -> c) -> (f :+: g) a b i -> c
caseD f g x = case x of
                Inl x -> f x
                Inr x -> g x