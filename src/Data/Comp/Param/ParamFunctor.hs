{-# LANGUAGE Rank2Types #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.ParamFunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Generalisation of 'MonadTrm'. However, due to a bug in GHC type
-- inference (http://hackage.haskell.org/trac/ghc/ticket/5600), the
-- function pmap can currently not be used to implement 'MonadTrm'.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.ParamFunctor 
    (ParamFunctor(..),pmap_) where


import Data.Maybe
import Unsafe.Coerce


class Functor f => ParamFunctor f where
    pmap :: forall g b .  ((forall a . g a) -> b) -> (forall a . f (g a)) -> f b
    

coercePmap :: ParamFunctor f => ((forall a . g a) -> b) -> (forall a . f (g a)) -> f b
{-# INLINE coercePmap #-}
coercePmap f t = fmap (unsafeCoerce f) t

{-# RULES
    "pmap/coerce" pmap = coercePmap
 #-}


instance ParamFunctor Maybe where
    pmap _ Nothing = Nothing
    pmap f x       = Just (f $ fromJust x)

instance ParamFunctor (Either a) where
    pmap _ (Left x) = Left x
    pmap f x        = Right (f $ fromRight x)
                             where fromRight :: Either a b -> b
                                   fromRight (Right x) = x
                                   fromRight _ = error "fromRight: Left"

instance ParamFunctor [] where
    pmap _ [] = []
    pmap f l  = f (head l) : pmap f (tail l)

