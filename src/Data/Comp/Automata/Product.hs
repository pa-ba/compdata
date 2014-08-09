{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Automata.Product
-- Copyright   :  (c) 2014 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.Automata.Product ((:<), pr) where



data Pos = Here | Le Pos | Ri Pos

data Res = NotFound | Ambiguous | Found Pos

type family Ch (l :: Res) (r :: Res) :: Res where
    Ch (Found x) (Found y) = Ambiguous
    Ch Ambiguous y = Ambiguous
    Ch x Ambiguous = Ambiguous
    Ch (Found x) y = Found (Le x)
    Ch x (Found y) = Found (Ri y)
    Ch x y = NotFound

type family Elem (e :: *) (p :: *) :: Res where
    Elem e e = Found Here
    Elem e (l,r) = Ch (Elem e l) (Elem e r)
    Elem e p = NotFound

data Proxy a = P

class IsElem (res :: Res) e p where
    pr' :: Proxy res -> p -> e

instance IsElem (Found Here) e e where
    pr' _ = id

instance IsElem (Found pos) e p => IsElem (Found (Le pos)) e (p, p') where
    pr' _ (x,_) = pr' (P :: Proxy (Found pos)) x

instance IsElem (Found pos) e p => IsElem (Found (Ri pos)) e (p', p) where
    pr' _ (_,y) = pr' (P :: Proxy (Found pos)) y


type (e :< p) = IsElem (Elem e p) e p

pr :: forall e p . (e :< p) => p -> e
pr = pr' (P :: Proxy (Elem e p))
