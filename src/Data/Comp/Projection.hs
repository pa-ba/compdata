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

module Data.Comp.Projection (pr, (:<)) where

import Data.Comp.SubsumeCommon

type family Elem (f :: *)
                 (g :: *) :: Emb where
    Elem f f = Found Here
    Elem (f1, f2) g =  Sum' (Elem f1 g) (Elem f2 g)
    Elem f (g1, g2) = Choose (Elem f g1) (Elem f g2)
    Elem f g = NotFound

class Proj (e :: Emb) (p :: *)
                         (q :: *) where
  pr'  :: Proxy e -> q -> p

instance Proj (Found Here) f f where
    pr' _ = id

instance Proj (Found p) f g => Proj (Found (Le p)) f (g, g') where
    pr' _ = pr' (P :: Proxy (Found p)) . fst


instance Proj (Found p) f g => Proj (Found (Ri p)) f (g', g) where
    pr' _ = pr' (P :: Proxy (Found p)) . snd


instance (Proj (Found p1) f1 g, Proj (Found p2) f2 g)
    => Proj (Found (Sum p1 p2)) (f1, f2) g where
    pr' _ x = (pr' (P :: Proxy (Found p1)) x, pr' (P :: Proxy (Found p2)) x)


infixl 5 :<
type f :< g = (Proj (ComprEmb (Elem f g)) f g)

pr :: forall p q . (p :< q) => q -> p
pr = pr' (P :: Proxy (ComprEmb (Elem p q)))
