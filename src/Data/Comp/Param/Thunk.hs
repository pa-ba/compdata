{-# LANGUAGE TypeOperators, FlexibleContexts, RankNTypes, GADTs #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Thunk
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines terms & contexts with thunks, with deferred
-- monadic computations.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Thunk
    (TermT
    ,TrmT
    ,CxtT
    ,Thunk
    ,thunk
    ,whnf
    ,whnf'
    ,whnfPr
    ,nf
    ,nfPr
    ,evalStrict
    ,AlgT
    ,strict
    ,strict')
 where

import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Algebra
import Data.Comp.Param.Ditraversable
import Data.Comp.Param.Difunctor

import Control.Monad

-- | This type represents terms with thunks.
type TermT m f = Term (Thunk m :+: f)

-- | This type represents terms with thunks.
type TrmT m f a = Trm  (Thunk m :+: f) a

-- | This type represents contexts with thunks.
type CxtT h  m f a = Cxt h (Thunk m :+: f) a

newtype Thunk m a b = Thunk (m b)

-- | This function turns a monadic computation into a thunk.
thunk :: (Thunk m :<: f) => m (Cxt h f a b) -> Cxt h f a b
thunk = inject . Thunk

-- | This function evaluates all thunks until a non-thunk node is
-- found.
whnf :: Monad m => TrmT m f a -> m (Either a (f a (TrmT m f a)))
whnf (Term (Inl (Thunk m))) = m >>= whnf
whnf (Term (Inr t)) = return $ Right t
whnf (Var x) = return $ Left x

whnf' :: Monad m => TermT m f -> m (TermT m f)
whnf'  = liftM (either Var inject) . whnf

-- | This function first evaluates the argument term into whnf via
-- 'whnf' and then projects the top-level signature to the desired
-- subsignature. Failure to do the projection is signalled as a
-- failure in the monad.
whnfPr :: (Monad m, g :<: f) => TermT m f -> m (g Any (TermT m f))
whnfPr t = do res <- whnf t
              case res of
                Left _  -> fail "cannot project variable"
                Right t ->
                    case proj t of
                      Just res' -> return res'
                      Nothing -> fail "projection failed"


-- | This function evaluates all thunks.
nf :: (Monad m, Ditraversable f m Any) => TermT m f -> m (Term f)
nf = either (return . Var) (liftM Term . dimapM nf) <=< whnf

-- | This function evaluates all thunks while simultaneously
-- projecting the term to a smaller signature. Failure to do the
-- projection is signalled as a failure in the monad as in 'whnfPr'.
nfPr :: (Monad m, Ditraversable g m Any, g :<: f) => TermT m f -> m (Term g)
nfPr = liftM Term . dimapM nfPr <=< whnfPr


evalStrict :: (Ditraversable g Maybe (TrmT m f a), 
               Ditraversable g m (TrmT m f a), Monad m, g :<: f) => 
              (g (TrmT m f a) (f a (TrmT m f a)) -> TrmT m f a)
           -> g (TrmT m f a) (TrmT m f a) -> TrmT m f a
evalStrict cont t = thunk $ do 
                      t' <- dimapM (liftM (either (const Nothing) Just) . whnf) t
                      case disequence t' of
                        Nothing -> return $ inject' t
                        Just s -> return $ cont s
                      

-- | This type represents algebras which have terms with thunks as
-- carrier.
type AlgT m f g = Alg f (TermT m g)

-- | This combinator makes the evaluation of the given functor
-- application strict by evaluating all thunks of immediate subterms.
strict :: (f :<: g, Ditraversable f m Any, Monad m) => f Any (TermT m g) -> TermT m g
strict x = thunk $ liftM inject $ dimapM whnf' x

-- | This combinator makes the evaluation of the given functor
-- application strict by evaluating all thunks of immediate subterms.
strict' :: (f :<: g, Ditraversable f m Any, Monad m) => f (TermT m g) (TermT m g) -> TermT m g
strict'  = strict . dimap Var id

-- -- | This type represents position representations for a functor
-- -- @f@. It is a function that extracts a number of components (of
-- -- polymorphic type @a@) from a functorial value and puts it into a
-- -- list.
-- type Pos f = forall a . Ord a => f a -> [a]

-- -- | This combinator is a variant of 'strict' that only makes a subset
-- -- of the arguments of a functor application strict. The first
-- -- argument of this combinator specifies which positions are supposed
-- -- to be strict.
-- strictAt :: (f :<: g, Traversable f, Zippable f, Monad m) => Pos f ->  f (TermT m g) -> TermT m g
-- strictAt p s = thunk $ liftM inject $ mapM run s'
--     where s'  = number s
--           isStrict e = Set.member e $ Set.fromList $ p s'
--           run e | isStrict e = whnf' $ unNumbered e
--                 | otherwise  = return $ unNumbered e
