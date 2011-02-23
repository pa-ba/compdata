--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use compositional data
-- types for mutually recursive data types. Examples of usage are provided
-- below.
--
--------------------------------------------------------------------------------
module Data.Comp.Multi (
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
    module Data.Comp.Multi.Term
  , module Data.Comp.Multi.Algebra
  , module Data.Comp.Multi.Functor
  , module Data.Comp.Multi.Sum
  , module Data.Comp.Multi.Product
    ) where

import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Functor
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Product

{- $ex1
The example below illustrates how to use generalised compositional data types 
to implement a small expression language, with a sub language of values, and 
an evaluation function mapping expressions to values.

The following language extensions are
needed in order to run the example: @TemplateHaskell@, @TypeOperators@,
@MultiParamTypeClasses@, @FlexibleInstances@, @FlexibleContexts@,
@UndecidableInstances@, and @GADTs@. Moreover, in order to derive instances for
GADTs, version 7 of GHC is needed.

> import Data.Comp.Multi
> import Data.Comp.Multi.HShow ()
> import Data.Comp.Derive
> 
> -- Signature for values and operators
> data Value e l where
>   Const  ::        Int -> Value e Int
>   Pair   :: e s -> e t -> Value e (s,t)
> data Op e l where
>   Add, Mult  :: e Int -> e Int   -> Op e Int
>   Fst        ::          e (s,t) -> Op e s
>   Snd        ::          e (s,t) -> Op e t
>
> -- Signature for the simple expression language
> type Sig = Op :++: Value
> 
> -- Derive boilerplate code using Template Haskell (GHC 7 needed)
> $(derive [instanceHFunctor, instanceHShowF, smartMConstructors] 
>          [''Value, ''Op])
> 
> -- Term evaluation algebra
> class Eval f v where
>   evalAlg :: HAlg f (HTerm v)
> 
> instance (Eval f v, Eval g v) => Eval (f :++: g) v where
>   evalAlg (HInl x) = evalAlg x
>   evalAlg (HInr x) = evalAlg x
> 
> -- Lift the evaluation algebra to a catamorphism
> eval :: (HFunctor f, Eval f v) => HTerm f :-> HTerm v
> eval = hcata evalAlg
> 
> instance (Value :<<: v) => Eval Value v where
>   evalAlg = hinject
> 
> instance (Value :<<: v) => Eval Op v where
>   evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
>   evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
>   evalAlg (Fst x)    = fst $ projP x
>   evalAlg (Snd x)    = snd $ projP x
> 
> projC :: (Value :<<: v) => HTerm v Int -> Int
> projC v = case hproject v of Just (Const n) -> n
> 
> projP :: (Value :<<: v) => HTerm v (s,t) -> (HTerm v s, HTerm v t)
> projP v = case hproject v of Just (Pair x y) -> (x,y)
> 
> -- Example: evalEx = iConst 2
> evalEx :: HTerm Value Int
> evalEx = eval (iFst $ iPair (iConst 2) (iConst 1) :: HTerm Sig Int)
-}

{- $ex2
The example below illustrates how to use generalised compositional data types to
implement a small expression language, with a sub language of values, and a 
monadic evaluation function mapping expressions to values.

The following language
extensions are needed in order to run the example: @TemplateHaskell@,
@TypeOperators@, @MultiParamTypeClasses@, @FlexibleInstances@,
@FlexibleContexts@, @UndecidableInstances@, and @GADTs@.  Moreover, in order to
derive instances for GADTs, version 7 of GHC is needed.

> import Data.Comp.Multi
> import Data.Comp.Multi.HShow ()
> import Data.Comp.Derive
> import Control.Monad (liftM)
> 
> -- Signature for values and operators
> data Value e l where
>   Const  ::        Int -> Value e Int
>   Pair   :: e s -> e t -> Value e (s,t)
> data Op e l where
>   Add, Mult  :: e Int -> e Int   -> Op e Int
>   Fst        ::          e (s,t) -> Op e s
>   Snd        ::          e (s,t) -> Op e t
> 
> -- Signature for the simple expression language
> type Sig = Op :++: Value
> 
> -- Derive boilerplate code using Template Haskell (GHC 7 needed)
> $(derive [instanceHFunctor, instanceHTraversable, instanceHFoldable,
>           instanceHEqF, instanceHShowF, smartMConstructors]
>          [''Value, ''Op])
> 
> -- Monadic term evaluation algebra
> class EvalM f v where
>   evalAlgM :: HAlgM Maybe f (HTerm v)
> 
> instance (EvalM f v, EvalM g v) => EvalM (f :++: g) v where
>   evalAlgM (HInl x) = evalAlgM x
>   evalAlgM (HInr x) = evalAlgM x
> 
> evalM :: (HTraversable f, EvalM f v) => HTerm f l
>                                      -> Maybe (HTerm v l)
> evalM = hcataM evalAlgM
> 
> instance (Value :<<: v) => EvalM Value v where
>   evalAlgM = return . hinject
> 
> instance (Value :<<: v) => EvalM Op v where
>   evalAlgM (Add x y)  = do n1 <- projC x
>                            n2 <- projC y
>                            return $ iConst $ n1 + n2
>   evalAlgM (Mult x y) = do n1 <- projC x
>                            n2 <- projC y
>                            return $ iConst $ n1 * n2
>   evalAlgM (Fst v)    = liftM fst $ projP v
>   evalAlgM (Snd v)    = liftM snd $ projP v
> 
> projC :: (Value :<<: v) => HTerm v Int -> Maybe Int
> projC v = case hproject v of
>             Just (Const n) -> return n; _ -> Nothing
> 
> projP :: (Value :<<: v) => HTerm v (a,b) -> Maybe (HTerm v a, HTerm v b)
> projP v = case hproject v of
>             Just (Pair x y) -> return (x,y); _ -> Nothing
> 
> -- Example: evalMEx = Just (iConst 5)
> evalMEx :: Maybe (HTerm Value Int)
> evalMEx = evalM ((iConst 1) `iAdd`
>                  (iConst 2 `iMult` iConst 2) :: HTerm Sig Int)
-}

{- $ex3
The example below illustrates how to compose a term homomorphism and an algebra,
exemplified via a desugaring term homomorphism and an evaluation algebra.

The following language extensions are needed in order to run the example:
@TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
@FlexibleInstances@, @FlexibleContexts@, @UndecidableInstances@, and @GADTs@. 
Moreover, in order to derive instances for GADTs, version 7 of GHC is needed.

> import Data.Comp.Multi
> import Data.Comp.Multi.HShow ()
> import Data.Comp.Derive
> 
> -- Signature for values, operators, and syntactic sugar
> data Value e l where
>   Const  ::        Int -> Value e Int
>   Pair   :: e s -> e t -> Value e (s,t)
> data Op e l where
>   Add, Mult  :: e Int -> e Int   -> Op e Int
>   Fst        ::          e (s,t) -> Op e s
>   Snd        ::          e (s,t) -> Op e t
> data Sugar e l where
>   Neg   :: e Int   -> Sugar e Int
>   Swap  :: e (s,t) -> Sugar e (t,s)
>
> -- Source position information (line number, column number)
> data Pos = Pos Int Int
>            deriving Show
> 
> -- Signature for the simple expression language
> type Sig = Op :++: Value
> type SigP = Op :&&: Pos :++: Value :&&: Pos
>
> -- Signature for the simple expression language, extended with syntactic sugar
> type Sig' = Sugar :++: Op :++: Value
> type SigP' = Sugar :&&: Pos :++: Op :&&: Pos :++: Value :&&: Pos
> 
> -- Derive boilerplate code using Template Haskell (GHC 7 needed)
> $(derive [instanceHFunctor, instanceHTraversable, instanceHFoldable,
>           instanceHEqF, instanceHShowF, smartMConstructors]
>          [''Value, ''Op, ''Sugar])
> 
> -- Term homomorphism for desugaring of terms
> class (HFunctor f, HFunctor g) => Desugar f g where
>   desugHom :: HTermHom f g
>   desugHom = desugHom' . hfmap HHole
>   desugHom' :: HAlg f (HContext g a)
>   desugHom' x = appHCxt (desugHom x)
> 
> instance (Desugar f h, Desugar g h) => Desugar (f :++: g) h where
>   desugHom (HInl x) = desugHom x
>   desugHom (HInr x) = desugHom x
>   desugHom' (HInl x) = desugHom' x
>   desugHom' (HInr x) = desugHom' x
> 
> instance (Value :<<: v, HFunctor v) => Desugar Value v where
>   desugHom = simpHCxt . hinj
> 
> instance (Op :<<: v, HFunctor v) => Desugar Op v where
>   desugHom = simpHCxt . hinj
> 
> instance (Op :<<: v, Value :<<: v, HFunctor v) => Desugar Sugar v where
>   desugHom' (Neg x)  = iConst (-1) `iMult` x
>   desugHom' (Swap x) = iSnd x `iPair` iFst x
>
> -- Term evaluation algebra
> class Eval f v where
>   evalAlg :: HAlg f (HTerm v)
> 
> instance (Eval f v, Eval g v) => Eval (f :++: g) v where
>   evalAlg (HInl x) = evalAlg x
>   evalAlg (HInr x) = evalAlg x
> 
> instance (Value :<<: v) => Eval Value v where
>   evalAlg = hinject
> 
> instance (Value :<<: v) => Eval Op v where
>   evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
>   evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
>   evalAlg (Fst x)    = fst $ projP x
>   evalAlg (Snd x)    = snd $ projP x
>
> projC :: (Value :<<: v) => HTerm v Int -> Int
> projC v = case hproject v of Just (Const n) -> n
>
> projP :: (Value :<<: v) => HTerm v (s,t) -> (HTerm v s, HTerm v t)
> projP v = case hproject v of Just (Pair x y) -> (x,y)
>
> -- Compose the evaluation algebra and the desugaring homomorphism to an
> -- algebra
> eval :: HTerm Sig' :-> HTerm Value
> eval = hcata (evalAlg `compHAlg` (desugHom :: HTermHom Sig' Sig))
> 
> -- Example: evalEx = iPair (iConst 2) (iConst 1)
> evalEx :: HTerm Value (Int,Int)
> evalEx = eval $ iSwap $ iPair (iConst 1) (iConst 2)
-}

{- $ex4
The example below illustrates how to lift a term homomorphism to products,
exemplified via a desugaring term homomorphism lifted to terms annotated with
source position information.

The following language extensions are needed in order to run the example:
@TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
@FlexibleInstances@, @FlexibleContexts@, @UndecidableInstances@, and @GADTs@.
 Moreover, in order to derive instances for GADTs, version 7 of GHC is needed.

> import Data.Comp.Multi
> import Data.Comp.Multi.HShow ()
> import Data.Comp.Derive
> 
> -- Signature for values, operators, and syntactic sugar
> data Value e l where
>   Const  ::        Int -> Value e Int
>   Pair   :: e s -> e t -> Value e (s,t)
> data Op e l where
>   Add, Mult  :: e Int -> e Int   -> Op e Int
>   Fst        ::          e (s,t) -> Op e s
>   Snd        ::          e (s,t) -> Op e t
> data Sugar e l where
>   Neg   :: e Int   -> Sugar e Int
>   Swap  :: e (s,t) -> Sugar e (t,s)
>
> -- Source position information (line number, column number)
> data Pos = Pos Int Int
>            deriving Show
> 
> -- Signature for the simple expression language
> type Sig = Op :++: Value
> type SigP = Op :&&: Pos :++: Value :&&: Pos
>
> -- Signature for the simple expression language, extended with syntactic sugar
> type Sig' = Sugar :++: Op :++: Value
> type SigP' = Sugar :&&: Pos :++: Op :&&: Pos :++: Value :&&: Pos
> 
> -- Derive boilerplate code using Template Haskell (GHC 7 needed)
> $(derive [instanceHFunctor, instanceHTraversable, instanceHFoldable,
>           instanceHEqF, instanceHShowF, smartMConstructors]
>          [''Value, ''Op, ''Sugar])
> 
> -- Term homomorphism for desugaring of terms
> class (HFunctor f, HFunctor g) => Desugar f g where
>   desugHom :: HTermHom f g
>   desugHom = desugHom' . hfmap HHole
>   desugHom' :: HAlg f (HContext g a)
>   desugHom' x = appHCxt (desugHom x)
> 
> instance (Desugar f h, Desugar g h) => Desugar (f :++: g) h where
>   desugHom (HInl x) = desugHom x
>   desugHom (HInr x) = desugHom x
>   desugHom' (HInl x) = desugHom' x
>   desugHom' (HInr x) = desugHom' x
> 
> instance (Value :<<: v, HFunctor v) => Desugar Value v where
>   desugHom = simpHCxt . hinj
> 
> instance (Op :<<: v, HFunctor v) => Desugar Op v where
>   desugHom = simpHCxt . hinj
> 
> instance (Op :<<: v, Value :<<: v, HFunctor v) => Desugar Sugar v where
>   desugHom' (Neg x)  = iConst (-1) `iMult` x
>   desugHom' (Swap x) = iSnd x `iPair` iFst x
>
> -- Lift the desugaring term homomorphism to a catamorphism
> desug :: HTerm Sig' :-> HTerm Sig
> desug = appHTermHom desugHom
>
> -- Example: desugEx = iPair (iConst 2) (iConst 1)
> desugEx :: HTerm Sig (Int,Int)
> desugEx = desug $ iSwap $ iPair (iConst 1) (iConst 2)
>
> -- Lift desugaring to terms annotated with source positions
> desugP :: HTerm SigP' :-> HTerm SigP
> desugP = appHTermHom (productHTermHom desugHom)
>
> iSwapP :: (HDistProd f p f', Sugar :<<: f) => p -> HTerm f' (a,b) -> HTerm f' (b,a)
> iSwapP p x = HTerm (hinjectP p $ hinj $ Swap x)
>
> iConstP :: (HDistProd f p f', Value :<<: f) => p -> Int -> HTerm f' Int
> iConstP p x = HTerm (hinjectP p $ hinj $ Const x)
>
> iPairP :: (HDistProd f p f', Value :<<: f) => p -> HTerm f' a -> HTerm f' b -> HTerm f' (a,b)
> iPairP p x y = HTerm (hinjectP p $ hinj $ Pair x y)
>
> iFstP :: (HDistProd f p f', Op :<<: f) => p -> HTerm f' (a,b) -> HTerm f' a
> iFstP p x = HTerm (hinjectP p $ hinj $ Fst x)
>
> iSndP :: (HDistProd f p f', Op :<<: f) => p -> HTerm f' (a,b) -> HTerm f' b
> iSndP p x = HTerm (hinjectP p $ hinj $ Snd x)
>
> -- Example: desugPEx = iPairP (Pos 1 0)
> --                            (iSndP (Pos 1 0) (iPairP (Pos 1 1)
> --                                                     (iConstP (Pos 1 2) 1)
> --                                                     (iConstP (Pos 1 3) 2)))
> --                            (iFstP (Pos 1 0) (iPairP (Pos 1 1)
> --                                                     (iConstP (Pos 1 2) 1)
> --                                                     (iConstP (Pos 1 3) 2)))
> desugPEx :: HTerm SigP (Int,Int)
> desugPEx = desugP $ iSwapP (Pos 1 0) (iPairP (Pos 1 1) (iConstP (Pos 1 2) 1)
>                                                        (iConstP (Pos 1 3) 2))
-}

{- $ex5
The example below illustrates how to use Higher-Order Abstract Syntax (HOAS)
with generalised compositional data types.

The following language extensions are needed in order to run the example:
@TemplateHaskell@, @TypeOperators@, @MultiParamTypeClasses@,
@FlexibleInstances@, @FlexibleContexts@, @UndecidableInstances@, and @GADTs@.
Moreover, in order to derive instances for GADTs, version 7 of GHC is needed.

> import Data.Comp.Multi
> import Data.Comp.Derive
> 
> data Value e l where
>   Const  ::        Int -> Value e Int
>   Pair   :: e s -> e t -> Value e (s,t)
> data Op e l where
>   Add, Mult  :: e Int -> e Int   -> Op e Int
>   Fst        ::          e (s,t) -> Op e s
>   Snd        ::          e (s,t) -> Op e t
> data Lam e l where
>   Lam :: (e l1 -> e l2) -> Lam e (l1 -> l2)
> data App e l where
>   App :: e (l1 -> l2) -> e l1 -> App e l2
>
> -- Signature for values
> type Val = Lam :++: Value
>
> -- Signature for expressions
> type Sig = App :++: Op :++: Val
> 
> -- Derive boilerplate code using Template Haskell (GHC 7 needed)
> $(derive [instanceHExpFunctor, smartMConstructors] 
>          [''Value, ''Op, ''Lam, ''App])
> 
> -- Term evaluation algebra
> class Eval f v where
>   evalAlg :: HAlg f (HTerm v)
> 
> instance (Eval f v, Eval g v) => Eval (f :++: g) v where
>   evalAlg (HInl x) = evalAlg x
>   evalAlg (HInr x) = evalAlg x
> 
> -- Lift the evaluation algebra to a catamorphism
> evalE :: (HExpFunctor f, Eval f v) => HTerm f :-> HTerm v
> evalE = hcataE evalAlg
> 
> instance (Value :<<: v) => Eval Value v where
>   evalAlg = hinject
> 
> instance (Value :<<: v) => Eval Op v where
>   evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
>   evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
>   evalAlg (Fst x)    = fst $ projP x
>   evalAlg (Snd x)    = snd $ projP x
>
> instance (Lam :<<: v) => Eval Lam v where
>   evalAlg = hinject
>
> instance (Lam :<<: v) => Eval App v where
>   evalAlg (App x y) = (projL x) y
>
> projC :: (Value :<<: v) => HTerm v Int -> Int
> projC v = case hproject v of Just (Const n) -> n
> 
> projP :: (Value :<<: v) => HTerm v (s,t) -> (HTerm v s, HTerm v t)
> projP v = case hproject v of Just (Pair x y) -> (x,y)
>
> projL :: (Lam :<<: v) => HTerm v (l1 -> l2) -> HTerm v l1 -> HTerm v l2
> projL v = case hproject v of Just (Lam f) -> f
> 
> -- Example: evalEEx = iConst 3
> evalEEx :: HTerm Val Int
> evalEEx = evalE (((iLam $ \x -> x) `iApp`
>                   (iConst 1 `iAdd` iConst 2)) :: HTerm Sig Int)
-}