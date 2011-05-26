{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FlexibleInstances,
FlexibleContexts, UndecidableInstances, TemplateHaskell, TypeOperators #-}
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
import Data.Comp.Ops
import Data.Comp.Show ()
import Control.Monad
import Data.Comp.Derive

{-| This function represents transition functions of
deterministic bottom-up tree transducers (DUTTs).  -}

type DUTT q f g = forall a. f (q,a) -> (q, Context g a)

{-| This function transforms a DUTT transition function into an
algebra.  -}

duttAlg :: (Functor g)  => DUTT q f g -> Alg f (q, Term g)
duttAlg trans = fmap injectCxt . trans 

{-| This function runs the given DUTT transition function on the given
term.  -}

runDUTT :: (Functor f, Functor g)  => DUTT q f g -> Term f -> (q, Term g)
runDUTT = cata . duttAlg

class State f q where
    state :: Alg f q


type GTermHom q f g = forall a . (a -> q) -> f a -> Context g a

toDUTT :: (Functor f, Functor g, State f q) => GTermHom q f g -> DUTT q f g
toDUTT f t = (q, c)
    where q = state $ fmap fst t
          c =  fmap snd $ f fst t


gTermHom :: (Functor f, Functor g, State f q) => GTermHom q f g -> Term f -> (q,Term g)
gTermHom h = runDUTT (toDUTT h)

data Str a = Str
data Base a = Char | List a

type Typ = Str :+: Base

$(derive [instanceFunctor,smartConstructors, instanceShowF] [''Str,''Base])

class StringType f g where
    strTypeHom :: GTermHom Bool f g

instance (StringType f h, StringType g h) => StringType(f :+: g) h where
    strTypeHom q (Inl x) = strTypeHom q x
    strTypeHom q (Inr x) = strTypeHom q x

strType :: (Base :<: f, Functor f, Functor g, StringType f g)
        => Term f -> Term g
strType = snd . gTermHom strTypeHom

instance (Base :<: f) => State f Bool where
    state f = case proj f of
                Just Char -> True
                _ -> False
    
instance (Str :<:  f, Functor f) =>  StringType Str f where
    strTypeHom _ = simpCxt . inj

instance (Str :<:  f, Base :<: f, Functor f) =>  StringType Base f where
    strTypeHom _ Char = iChar
    strTypeHom q (List t) = if q t then iStr 
                                   else iList $ Hole t


ex1 :: Term Typ
ex1 = iList iChar

runEx1 :: Term Typ
runEx1 = strType ex1