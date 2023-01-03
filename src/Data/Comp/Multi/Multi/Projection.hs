{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE RankNTypes #-}



--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Projection
-- Copyright   :  (c) 2014 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides a generic projection function 'pr' for
-- arbitrary nested binary products.
--
--------------------------------------------------------------------------------


module Data.Comp.Multi.Multi.Projection (pr, (:<), (:**:)(..), hffst, hfsnd) where

import Data.Comp.SubsumeCommon
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Ops

class Proj (e :: Emb) (p :: (* -> *) -> * -> *)
                      (q :: (* -> *) -> * -> *) where
    pr'  :: Proxy e -> q a :-> p a

instance Proj (Found Here) f f where
    pr' _ = id

instance Proj (Found p) f g => Proj (Found (Le p)) f (g :**: g') where
    pr' _ = pr' (P :: Proxy (Found p)) . hffst


instance Proj (Found p) f g => Proj (Found (Ri p)) f (g' :**: g) where
    pr' _ = pr' (P :: Proxy (Found p)) . hfsnd


instance (Proj (Found p1) f1 g, Proj (Found p2) f2 g)
    => Proj (Found (Sum p1 p2)) (f1 :**: f2) g where
    pr' _ x = pr' (P :: Proxy (Found p1)) x :**: pr' (P :: Proxy (Found p2)) x


infixl 5 :<

-- | The constraint @e :< p@ expresses that @e@ is a component of the
-- type @p@. That is, @p@ is formed by binary products using the type
-- @e@. The occurrence of @e@ must be unique. For example we have @Int
-- :< (Bool,(Int,Bool))@ but not @Bool :< (Bool,(Int,Bool))@.

type f :< g = (Proj (ComprEmb (Elem f g)) f g)


-- | This function projects the component of type @e@ out or the
-- compound value of type @p@.

pr :: forall p q a . (p :< q) => q a :-> p a
pr = pr' (P :: Proxy (ComprEmb (Elem p q)))
