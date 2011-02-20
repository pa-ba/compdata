--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use
-- /Compositional Data Types/. Compositional Data Types is an extension of
-- Wouter Swierstra's Functional Pearl: /Data types a la carte/. Examples of
-- usage are provided below.
--
--------------------------------------------------------------------------------
module Data.Comp(
  -- * Examples
  -- ** Pure Computations
  -- $ex1

  -- ** Monadic Computations
  -- $ex2

  -- ** Composing Term Homomorphisms and Algebras
  -- $ex3

  -- ** Lifting Term Homomorphisms to Products
  -- $ex4

  -- ** Higher-Order Abstract Syntax
  -- $ex5
    module Data.Comp.Term
  , module Data.Comp.Algebra
  , module Data.Comp.Sum
  , module Data.Comp.Product
  , module Data.Comp.Equality
  , module Data.Comp.Ordering
  , module Data.Comp.Generic
    ) where

import Data.Comp.Term
import Data.Comp.Algebra
import Data.Comp.Sum
import Data.Comp.Product
import Data.Comp.Equality
import Data.Comp.Ordering
import Data.Comp.Generic

{- $ex1
The example below illustrates how to use compositional data types to implement
a small expression language, with a sub language of values, and an evaluation
function mapping expressions to values.

The following language extensions are
needed in order to run the example: @TemplateHaskell@, @TypeOperators@,
@MultiParamTypeClasses@, @FlexibleInstances@, @FlexibleContexts@, and
@UndecidableInstances@.

> import Data.Comp
> import Data.Comp.Show ()
> import Data.Comp.Derive
> 
> -- Signature for values and operators
> data Value e = Const Int | Pair e e
> data Op e = Add e e | Mult e e | Fst e | Snd e
> 
> -- Signature for the simple expression language
> type Sig = Op :+: Value
> 
> -- Derive boilerplate code using Template Haskell
> $(derive [instanceFunctor, instanceShowF, smartConstructors] [''Value, ''Op])
> 
> -- Term evaluation algebra
> class Eval f v where
>   evalAlg :: Alg f (Term v)
> 
> instance (Eval f v, Eval g v) => Eval (f :+: g) v where
>   evalAlg (Inl x) = evalAlg x
>   evalAlg (Inr x) = evalAlg x
> 
> -- Lift the evaluation algebra to a catamorphism
> eval :: (Functor f, Eval f v) => Term f -> Term v
> eval = cata evalAlg
> 
> instance (Value :<: v) => Eval Value v where
>   evalAlg = inject
> 
> instance (Value :<: v) => Eval Op v where
>   evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
>   evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
>   evalAlg (Fst x)    = fst $ projP x
>   evalAlg (Snd x)    = snd $ projP x
> 
> projC :: (Value :<: v) => Term v -> Int
> projC v = let Just (Const n) = project v in n
> 
> projP :: (Value :<: v) => Term v -> (Term v, Term v)
> projP v = let Just (Pair x y) = project v in (x,y)
> 
> -- Example: evalEx = iConst 5
> evalEx :: Term Value
> evalEx = eval ((iConst 1) `iAdd` (iConst 2 `iMult` iConst 2) :: Term Sig)
-}

{- $ex2
The example below illustrates how to use compositional data types to implement
a small expression language, with a sub language of values, and a monadic
evaluation function mapping expressions to values.

The following language
extensions are needed in order to run the example: @TemplateHaskell@,
@TypeOperators@, @MultiParamTypeClasses@, @FlexibleInstances@,
@FlexibleContexts@, and @UndecidableInstances@.

> import Data.Comp
> import Data.Comp.Derive
> import Control.Monad (liftM)
> 
> -- Signature for values and operators
> data Value e = Const Int | Pair e e
> data Op e = Add e e | Mult e e | Fst e | Snd e
> 
> -- Signature for the simple expression language
> type Sig = Op :+: Value
> 
> -- Derive boilerplate code using Template Haskell
> $(derive [instanceFunctor, instanceTraversable, instanceFoldable,
>           instanceEqF, instanceShowF, smartConstructors]
>          [''Value, ''Op])
> 
> -- Monadic term evaluation algebra
> class EvalM f v where
>   evalAlgM :: AlgM Maybe f (Term v)
> 
> instance (EvalM f v, EvalM g v) => EvalM (f :+: g) v where
>   evalAlgM (Inl x) = evalAlgM x
>   evalAlgM (Inr x) = evalAlgM x
> 
> -- Lift the monadic evaluation algebra to a monadic catamorphism
> evalM :: (Traversable f, EvalM f v) => Term f -> Maybe (Term v)
> evalM = cataM evalAlgM
> 
> instance (Value :<: v) => EvalM Value v where
>   evalAlgM = return . inject
> 
> instance (Value :<: v) => EvalM Op v where
>   evalAlgM (Add x y)  = do n1 <- projC x
>                            n2 <- projC y
>                            return $ iConst $ n1 + n2
>   evalAlgM (Mult x y) = do n1 <- projC x
>                            n2 <- projC y
>                            return $ iConst $ n1 * n2
>   evalAlgM (Fst v)    = liftM fst $ projP v
>   evalAlgM (Snd v)    = liftM snd $ projP v
> 
> projC :: (Value :<: v) => Term v -> Maybe Int
> projC v = case project v of
>             Just (Const n) -> return n
>             _ -> Nothing
> 
> projP :: (Value :<: v) => Term v -> Maybe (Term v, Term v)
> projP v = case project v of
>             Just (Pair x y) -> return (x,y)
>             _ -> Nothing
> 
> -- Example: evalMEx = Just (iConst 5)
> evalMEx :: Maybe (Term Value)
> evalMEx = evalM ((iConst 1) `iAdd` (iConst 2 `iMult` iConst 2) :: Term Sig)
-}

{- $ex3
The example below illustrates how to compose a term homomorphism and an algebra,
exemplified via a desugaring term homomorphism and an evaluation algebra.

The following language extensions are needed in order to run the example:
@TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
@FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.

> import Data.Comp
> import Data.Comp.Show ()
> import Data.Comp.Derive
> 
> -- Signature for values, operators, and syntactic sugar
> data Value e = Const Int | Pair e e
> data Op e = Add e e | Mult e e | Fst e | Snd e
> data Sugar e = Neg e | Swap e
>
> -- Source position information (line number, column number)
> data Pos = Pos Int Int
>            deriving Show
> 
> -- Signature for the simple expression language
> type Sig = Op :+: Value
> type SigP = Op :&: Pos :+: Value :&: Pos
>
> -- Signature for the simple expression language, extended with syntactic sugar
> type Sig' = Sugar :+: Op :+: Value
> type SigP' = Sugar :&: Pos :+: Op :&: Pos :+: Value :&: Pos
>
> -- Derive boilerplate code using Template Haskell
> $(derive [instanceFunctor, instanceTraversable, instanceFoldable,
>           instanceEqF, instanceShowF, smartConstructors]
>          [''Value, ''Op, ''Sugar])
> 
> -- Term homomorphism for desugaring of terms
> class (Functor f, Functor g) => Desugar f g where
>   desugHom :: TermHom f g
>   desugHom = desugHom' . fmap Hole
>   desugHom' :: Alg f (Context g a)
>   desugHom' x = appCxt (desugHom x)
> 
> instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
>   desugHom (Inl x) = desugHom x
>   desugHom (Inr x) = desugHom x
>   desugHom' (Inl x) = desugHom' x
>   desugHom' (Inr x) = desugHom' x
> 
> instance (Value :<: v, Functor v) => Desugar Value v where
>   desugHom = simpCxt . inj
> 
> instance (Op :<: v, Functor v) => Desugar Op v where
>   desugHom = simpCxt . inj
> 
> instance (Op :<: v, Value :<: v, Functor v) => Desugar Sugar v where
>   desugHom' (Neg x)  = iConst (-1) `iMult` x
>   desugHom' (Swap x) = iSnd x `iPair` iFst x
>
> -- Term evaluation algebra
> class Eval f v where
>   evalAlg :: Alg f (Term v)
> 
> instance (Eval f v, Eval g v) => Eval (f :+: g) v where
>   evalAlg (Inl x) = evalAlg x
>   evalAlg (Inr x) = evalAlg x
> 
> instance (Value :<: v) => Eval Value v where
>   evalAlg = inject
> 
> instance (Value :<: v) => Eval Op v where
>   evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
>   evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
>   evalAlg (Fst x)    = fst $ projP x
>   evalAlg (Snd x)    = snd $ projP x
> 
> projC :: (Value :<: v) => Term v -> Int
> projC v = let Just (Const n) = project v in n
> 
> projP :: (Value :<: v) => Term v -> (Term v, Term v)
> projP v = let Just (Pair x y) = project v in (x,y)
>
> -- Compose the evaluation algebra and the desugaring homomorphism to an
> -- algebra
> eval :: Term Sig' -> Term Value
> eval = cata (evalAlg `compAlg` (desugHom :: TermHom Sig' Sig))
> 
> -- Example: evalEx = iPair (iConst 2) (iConst 1)
> evalEx :: Term Value
> evalEx = eval $ iSwap $ iPair (iConst 1) (iConst 2)
-}

{- $ex4
The example below illustrates how to lift a term homomorphism to products,
exemplified via a desugaring term homomorphism lifted to terms annotated with
source position information.

The following language extensions are needed in order to run the example:
@TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
@FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.

> import Data.Comp
> import Data.Comp.Show ()
> import Data.Comp.Derive
> 
> -- Signature for values, operators, and syntactic sugar
> data Value e = Const Int | Pair e e
> data Op e = Add e e | Mult e e | Fst e | Snd e
> data Sugar e = Neg e | Swap e
>
> -- Source position information (line number, column number)
> data Pos = Pos Int Int
>            deriving Show
> 
> -- Signature for the simple expression language
> type Sig = Op :+: Value
> type SigP = Op :&: Pos :+: Value :&: Pos
>
> -- Signature for the simple expression language, extended with syntactic sugar
> type Sig' = Sugar :+: Op :+: Value
> type SigP' = Sugar :&: Pos :+: Op :&: Pos :+: Value :&: Pos
>
> -- Derive boilerplate code using Template Haskell
> $(derive [instanceFunctor, instanceTraversable, instanceFoldable,
>           instanceEqF, instanceShowF, smartConstructors]
>          [''Value, ''Op, ''Sugar])
> 
> -- Term homomorphism for desugaring of terms
> class (Functor f, Functor g) => Desugar f g where
>   desugHom :: TermHom f g
>   desugHom = desugHom' . fmap Hole
>   desugHom' :: Alg f (Context g a)
>   desugHom' x = appCxt (desugHom x)
> 
> instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
>   desugHom (Inl x) = desugHom x
>   desugHom (Inr x) = desugHom x
>   desugHom' (Inl x) = desugHom' x
>   desugHom' (Inr x) = desugHom' x
> 
> instance (Value :<: v, Functor v) => Desugar Value v where
>   desugHom = simpCxt . inj
> 
> instance (Op :<: v, Functor v) => Desugar Op v where
>   desugHom = simpCxt . inj
> 
> instance (Op :<: v, Value :<: v, Functor v) => Desugar Sugar v where
>   desugHom' (Neg x)  = iConst (-1) `iMult` x
>   desugHom' (Swap x) = iSnd x `iPair` iFst x
> 
> -- Lift the desugaring term homomorphism to a catamorphism
> desug :: Term Sig' -> Term Sig
> desug = appTermHom desugHom
>
> -- Example: desugEx = iPair (iConst 2) (iConst 1)
> desugEx :: Term Sig
> desugEx = desug $ iSwap $ iPair (iConst 1) (iConst 2)
>
> -- Lift desugaring to terms annotated with source positions
> desugP :: Term SigP' -> Term SigP
> desugP = appTermHom (productTermHom desugHom)
>
> iSwapP :: (DistProd f p f', Sugar :<: f) => p -> Term f' -> Term f'
> iSwapP p x = Term (injectP p $ inj $ Swap x)
>
> iConstP :: (DistProd f p f', Value :<: f) => p -> Int -> Term f'
> iConstP p x = Term (injectP p $ inj $ Const x)
>
> iPairP :: (DistProd f p f', Value :<: f) => p -> Term f' -> Term f' -> Term f'
> iPairP p x y = Term (injectP p $ inj $ Pair x y)
>
> iFstP :: (DistProd f p f', Op :<: f) => p -> Term f' -> Term f'
> iFstP p x = Term (injectP p $ inj $ Fst x)
>
> iSndP :: (DistProd f p f', Op :<: f) => p -> Term f' -> Term f'
> iSndP p x = Term (injectP p $ inj $ Snd x)
>
> -- Example: desugPEx = iPairP (Pos 1 0)
> --                            (iSndP (Pos 1 0) (iPairP (Pos 1 1)
> --                                                     (iConstP (Pos 1 2) 1)
> --                                                     (iConstP (Pos 1 3) 2)))
> --                            (iFstP (Pos 1 0) (iPairP (Pos 1 1)
> --                                                     (iConstP (Pos 1 2) 1)
> --                                                     (iConstP (Pos 1 3) 2)))
> desugPEx :: Term SigP
> desugPEx = desugP $ iSwapP (Pos 1 0) (iPairP (Pos 1 1) (iConstP (Pos 1 2) 1)
>                                                        (iConstP (Pos 1 3) 2))
-}

{- $ex5
The example below illustrates how to use Higher-Order Abstract Syntax (HOAS)
with compositional data types.

The following language extensions are needed in order to run the example:
@TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
@FlexibleInstances@, @FlexibleContexts@, and @UndecidableInstances@.

> import Data.Comp
> import Data.Comp.Show ()
> import Data.Comp.Derive
> 
> -- Signature for values, operators, lambda functions, and applications
> data Value e = Const Int | Pair e e
> data Op e = Add e e | Mult e e | Fst e | Snd e
> data Lam e = Lam (e -> e)
> data App e = App e e
> 
> -- Signature for the extended expression language
> type Val = Lam :+: Value
> type Sig = App :+: Op :+: Val
>
> -- Derive boilerplate code using Template Haskell
> $(derive [instanceExpFunctor, smartConstructors]
>          [''Value, ''Op, ''Lam, ''App])
> $(derive [instanceFunctor, instanceFoldable,
>           instanceTraversable, instanceShowF] [''Value])
> 
> -- Term evaluation algebra
> class Eval f v where
>   evalAlg :: Alg f (Term v)
> 
> instance (Eval f v, Eval g v) => Eval (f :+: g) v where
>   evalAlg (Inl x) = evalAlg x
>   evalAlg (Inr x) = evalAlg x
> 
> instance (Value :<: v) => Eval Value v where
>   evalAlg = inject
> 
> instance (Value :<: v) => Eval Op v where
>   evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
>   evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
>   evalAlg (Fst x)    = fst $ projP x
>   evalAlg (Snd x)    = snd $ projP x
>
> instance (Lam :<: v) => Eval Lam v where
>   evalAlg = inject
> 
> instance (Lam :<: v) => Eval App v where
>   evalAlg (App x y) = (projL x) y
> 
> projC :: (Value :<: v) => Term v -> Int
> projC v = let Just (Const n) = project v in n
> 
> projP :: (Value :<: v) => Term v -> (Term v, Term v)
> projP v = let Just (Pair x y) = project v in (x,y)
>
> projL :: (Lam :<: v) => Term v -> Term v -> Term v
> projL v = let Just (Lam f) = project v in f
>
> -- Lift the evaluation algebra to a catamorphism. Note the use of 'cataE'
> -- instead of 'cata'.
> eval :: (ExpFunctor f, Eval f v) => Term f -> Term v
> eval = cataE evalAlg
>
> -- Example: evalEx = Just (iConst 3). Note that we need to project the value
> -- to a value without HOAS in order to print it with 'showF'.
> evalEx :: Maybe (Term Value)
> evalEx = deepProject' $ (eval e :: Term Val)
>     where e :: Term Sig
>           e = (iLam $ \x -> x) `iApp` (iConst 1 `iAdd` iConst 2)
-}