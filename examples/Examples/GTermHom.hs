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

type Transducer q f g = forall a. f (q,a) -> (q, Context g a)

{-| This function transforms a Transducer transition function into an
algebra.  -}

duttAlg :: (Functor g)  => Transducer q f g -> Alg f (q, Term g)
duttAlg trans = fmap appCxt . trans 

{-| This function runs the given Transducer transition function on the given
term.  -}

runTransducer :: (Functor f, Functor g) => Transducer q f g -> Term f -> (q, Term g)
runTransducer = cata . duttAlg


runTransducer' :: (Functor f, Functor g) => (a -> q) -> Transducer q f g -> Context f a -> (q, Context g a)
runTransducer' st trans = run where
    run (Hole a) = (st a, Hole a)
    run (Term t) = fmap appCxt $ trans $ fmap run t
    
compTransducer :: (Functor f, Functor g, Functor h)
               => Transducer q2 g h -> Transducer q1 f g -> Transducer (q1,q2) f h
compTransducer t2 t1 x = ((q1,q2), fmap snd c2) where
    (q1, c1) = t1 $ fmap (\((q1,q2),a) -> (q1,(q2,a))) x
    (q2, c2) = runTransducer' fst t2 c1

type GTermHom q f g = forall a . (?state :: a -> q) => f a -> Context g a

toTransducer :: (Functor f, Functor g) => Alg f q -> GTermHom q f g -> Transducer q f g
toTransducer alg f t = (q, c)
    where q = alg $ fmap fst t
          c =  fmap snd $ (let ?state = fst in f t)


gTermHom :: (Functor f, Functor g) => Alg f q -> GTermHom q f g -> Term f -> (q,Term g)
gTermHom alg h = runTransducer (toTransducer alg h)

gTermHom' :: (Functor f, Functor g) => (a -> q) -> Alg f q -> GTermHom q f g -> Context f a -> (q, Context g a)
gTermHom' st alg h = runTransducer' st (toTransducer alg h)
          

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
               | ?state t  = iStr 
               | otherwise = iList $ Hole t


ex1 :: Term Typ
ex1 = iList iChar

runEx1 :: Term Typ
runEx1 = strType ex1