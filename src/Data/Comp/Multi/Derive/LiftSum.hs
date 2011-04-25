{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for higher-order functors to sums of higher-order
-- functors.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Derive.LiftSum
    (
     liftSum,
     caseH
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Ops ((:+:)(..))

{-| Given the name of a type class, where the first parameter is a higher-order
  functor, lift it to sums of higher-order. Example: @class HShowF f where ...@
  is lifted as @instance (HShowF f, HShowF g) => HShowF (f :+: g) where ... @.
 -}
liftSum :: Name -> Q [Dec]
liftSum fname = do
  ClassI (ClassD _ name targs _ decs) _ <- abstractNewtypeQ $ reify fname
  targs' <- newNames (length targs - 1) "x"
  f <- newName "f"
  g <- newName "g"
  let cxt = [ClassP name (map VarT $ f : targs'),
             ClassP name (map VarT $ g : targs')]
  let tp = ConT name `AppT` ((ConT ''(:+:) `AppT` VarT f) `AppT` VarT g)
  let complType = foldl (\a x -> a `AppT` VarT x) tp targs'
  decs' <- sequence $ concatMap decl decs
  return [InstanceD cxt complType decs']
      where decl :: Dec -> [DecQ]
            decl (SigD f _) = [funD f [clause f]]
            decl _ = []
            clause :: Name -> ClauseQ
            clause f = do x <- newName "x"
                          b <- normalB [|caseH $(varE f) $(varE f) $(varE x)|]
                          return $ Clause [VarP x] b []

{-| Utility function to case on a higher-order functor sum, without exposing the
  internal representation of sums. -}
caseH :: (f a b -> c) -> (g a b -> c) -> (f :+: g) a b -> c
caseH f g x = case x of
                Inl x -> f x
                Inr x -> g x