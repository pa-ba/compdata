{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FlexibleInstances,
FlexibleContexts, UndecidableInstances, TemplateHaskell, TypeOperators, ImplicitParams, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.GTermHom
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Examples.GTermHom where

import Data.Comp
import Data.Comp.Show ()
import Control.Monad
import Data.Comp.Derive

{-| This function represents transition functions of
deterministic bottom-up tree transducers (DUTTs).  -}

type UpTrans q f g = forall a. f (q,a) -> (q, Context g a)

{-| This function transforms a UpTrans transition function into an
algebra.  -}

duttAlg :: (Functor g)  => UpTrans q f g -> Alg f (q, Term g)
duttAlg trans = fmap appCxt . trans 

{-| This function runs the given UpTrans transition function on the given
term.  -}

runUpTrans :: (Functor f, Functor g) => UpTrans q f g -> Term f -> (q, Term g)
runUpTrans = cata . duttAlg


runUpTrans' :: (Functor f, Functor g) => (a -> q) -> UpTrans q f g -> Context f a -> (q, Context g a)
runUpTrans' st trans = run where
    run (Hole a) = (st a, Hole a)
    run (Term t) = fmap appCxt $ trans $ fmap run t
    
compUpTrans :: (Functor f, Functor g, Functor h)
               => UpTrans q2 g h -> UpTrans q1 f g -> UpTrans (q1,q2) f h
compUpTrans t2 t1 x = ((q1,q2), fmap snd c2) where
    (q1, c1) = t1 $ fmap (\((q1,q2),a) -> (q1,(q2,a))) x
    (q2, c2) = runUpTrans' fst t2 c1

type GTermHom q f g = forall a . (?below :: a -> q, ?above :: q) => f a -> Context g a

toUpTrans :: (Functor f, Functor g) => Alg f q -> GTermHom q f g -> UpTrans q f g
toUpTrans alg f t = (q, c)
    where q = alg $ fmap fst t
          c =  fmap snd $ (let ?below = fst; ?above = q in f t)


gTermHom :: (Functor f, Functor g) => Alg f q -> GTermHom q f g -> Term f -> (q,Term g)
gTermHom alg h = runUpTrans (toUpTrans alg h)

gTermHom' :: (Functor f, Functor g) => (a -> q) -> Alg f q -> GTermHom q f g -> Context f a -> (q, Context g a)
gTermHom' st alg h = runUpTrans' st (toUpTrans alg h)
          

data Str a = Str
data Base a = Char | List a

type Typ = Str :+: Base

$(derive [instanceFunctor,smartConstructors, instanceShowF] [''Str,''Base])

class StringType f g where
    strTypeHom :: GTermHom Bool f g

$(derive [liftSum] [''StringType])

strType :: (Base :<: f, Functor f, Functor g, StringType f g)
        => Term f -> Term g
strType = snd . gTermHom isCharAlg strTypeHom

isCharAlg :: (Base :<: f) => Alg f Bool
isCharAlg t = case proj t of
                Just Char -> True
                _ -> False
    
instance (Str :<: f, Functor f) =>  StringType Str f where
    strTypeHom = simpCxt . inj

instance (Str :<:  f, Base :<: f, Functor f) =>  StringType Base f where
    strTypeHom Char = iChar
    strTypeHom (List t)
               | ?below t  = iStr 
               | otherwise = iList $ Hole t


ex1 :: Term Typ
ex1 = iList iChar

runEx1 :: Term Typ
runEx1 = strType ex1