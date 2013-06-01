{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MacroAutomata
-- Copyright   :  (c) 2013 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.MacroAutomata where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Automata
import Data.Comp.Ops

-- | This type represents total deterministic macro tree transducers
-- (MTTs).

type MacroTrans f q g = forall a. q a -> f (q (Context g a) -> a) -> Context g a

-- | This is a variant of the type 'MacroTrans' that makes it easier
-- to define MTTs as it avoids the explicit use of 'Hole' when using
-- placeholders in the result.

type MacroTrans' f q g = forall a . q (Context g a) -> f (q (Context g a) -> Context g a)
                                 -> Context g a

mkMacroTrans :: (Functor f, Functor q) => MacroTrans' f q g -> MacroTrans f q g
mkMacroTrans tr q t = tr (fmap Hole q) (fmap (Hole .) t)

runMacroTrans :: (Functor g, Functor f, Functor q) => 
                 MacroTrans f q g -> q (Cxt h g a) -> Cxt h f a -> Cxt h g a
runMacroTrans tr q t = run t q where
    run (Term t) q = appCxt (tr q (fmap run' t))
    run (Hole a) _ = Hole a
    run' t q = run t (fmap appCxt q)
    

runMacroTrans' :: forall g f q h a. 
                  (Functor g, Functor f, Functor q) => MacroTrans f q g -> q (Cxt h g a) 
               -> Cxt h f (q (Cxt h g a) -> a) -> Cxt h g a
runMacroTrans' tr q t = run t q where
    run :: Cxt h f (q (Cxt h g a) -> a) -> q (Cxt h g a) -> Cxt h g a
    run (Term t) q = appCxt (tr q (fmap run' t))
    run (Hole a) q = Hole (a q)

    run' :: Cxt h f (q (Cxt h g a) -> a) -> q (Context g (Cxt h g a)) -> Cxt h g a
    run' t q = run t (fmap appCxt q)

compMacroDown :: (Functor f, Functor g, Functor h, Functor p)
              => MacroTrans g p h -> DownTrans f q g -> MacroTrans f (p :&: q) h
compMacroDown t2 t1 (p :&: q) t = runMacroTrans' t2 (fmap Hole p) (t1 q (fmap curryF t))
    where curryF :: ((p :&: q) a -> b) -> q -> p a -> b
          curryF f q p = f (p :&: q)

runDownTrans' :: (Functor f, Functor g) => DownTrans f q g -> q -> Cxt h f (q -> a) -> Cxt h g a
runDownTrans' tr q (Term t) = appCxt $ tr q $ fmap (\s q -> runDownTrans' tr q s) t
runDownTrans' _ q (Hole a) = Hole (a q)



data (q :^: p) a = q (p -> a) :^: p

instance Functor q => Functor (q :^: p) where
    fmap f (q :^: p) = fmap (f .) q :^: p

compDownMacro :: forall f g h q p . (Functor f, Functor g, Functor h, Functor q)
              => DownTrans g p h -> MacroTrans f q g -> MacroTrans f (q :^: p) h
compDownMacro t2 t1 (q :^: p) t = runDownTrans' t2 p (t1 (fmap (\a p' -> a p') q) (fmap reshape t))
    where reshape :: ((q :^: p) (Context h a) -> a) -> (q (Context g (p -> a)) -> p -> a)
          reshape f q' p' = f (fmap (\s p'' -> runDownTrans' t2 p'' s) q' :^: p')


type MacroTransId  f g = forall a. a           -> f (Context g a -> a)           -> Context g a
type MacroTransId' f g = forall a. Context g a -> f (Context g a -> Context g a) -> Context g a

data Id a = Id {unId :: a} 

instance Functor Id where
    fmap f (Id x) = Id (f x)

macroTransId :: Functor f => MacroTransId f g -> MacroTrans f Id g
macroTransId tr (Id a) t = tr a (fmap (. Id) t)

macroTransId' :: Functor f => MacroTransId' f g -> MacroTrans f Id g
macroTransId' tr (Id a) t = tr (Hole a) (fmap (\f -> Hole . f . Id) t)

-- macro tree transducers with regular look-ahead
type MacroTransLA  f q p g = forall a. q a             -> p -> 
                             f (q (Context g a) -> a,           p) -> Context g a
type MacroTransLA' f q p g = forall a. q (Context g a) -> p -> 
                             f (q (Context g a) -> Context g a, p) -> Context g a

macroTransLA :: (Functor q, Functor f) => MacroTransLA' f q p g -> MacroTransLA f q p g
macroTransLA tr q p t = tr (fmap Hole q) p (fmap (\ (f, p) -> (Hole . f,p)) t)

runMacroTransLA :: forall g f q p. (Functor g, Functor f, Functor q) => 
                   UpState f p -> MacroTransLA f q p g -> q (Term g) -> Term f -> Term g
runMacroTransLA st tr q t = fst (run t) q where
    run :: Term f -> (q (Term g) -> Term g, p)
    run (Term t) = let p = st $ fmap snd t'
                       t' = fmap run' t
                   in (\ q -> appCxt (tr q p t'), p)
    run' :: Term f -> (q (Context g (Term g)) -> (Term g), p)
    run' t = let (res, p) = run t
             in  (res . fmap appCxt, p)
