infixr 5 :++:

data (f :++: g) (e :: * -> *) (t :: *) = HInl (f e t) | HInr (g e t)

instance (HFunctor f, HFunctor g) => HFunctor (f :++: g) where
    hmap f (HInl v) = HInl $ hmap f v
    hmap f (HInr v) = HInr $ hmap f v