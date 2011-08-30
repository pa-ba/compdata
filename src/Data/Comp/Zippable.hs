--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Zippable
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.Zippable
    ( module Data.Comp.Zippable
    , module Data.Stream ) where

import Data.Stream (Stream(..), (<:>))

-- | Instances of this class provide a generalisation of the zip
-- function on the list functor.
class Functor f => Zippable f where
    fzip :: Stream a -> f b -> f (a,b)
    fzip = fzipWith (\ x y -> (x,y))
    fzipWith :: (a -> b -> c) -> Stream a -> f b -> f c
    fzipWith f s l = fmap (uncurry f) (fzip s l)

-- | This type is used for applying a DDTAs.
newtype Numbered a = Numbered (Int, a)

unNumbered :: Numbered a -> a
unNumbered (Numbered (_, x)) = x

instance Eq (Numbered a) where
    Numbered (i,_) == Numbered (j,_) = i == j

instance Ord (Numbered a) where
    compare (Numbered (i,_))  (Numbered (j,_)) = i `compare` j


number :: Zippable f => f a -> f (Numbered a)
number t = fzipWith (curry Numbered) (nums 0) t
    where nums x = x `Cons` nums (x+1)

number' :: Zippable f => f a -> f (Int, a)
number' t = fzipWith num (nums 0) t
    where nums x = x <:> nums (x+1)
          num n a = (n,a)

instance Zippable [] where
    fzip (Cons x xs) (y:ys) = (x,y) : fzip xs ys
    fzip _ []  = []
    fzipWith f (Cons x xs) (y:ys) = f x y : fzipWith f xs ys
    fzipWith _ _ [] = []