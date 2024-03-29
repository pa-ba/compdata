{-# LANGUAGE
  TemplateHaskell,
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  TypeOperators,
  ScopedTypeVariables,
  TypeSynonymInstances,
  ConstraintKinds,
  CPP #-}

module Functions.Comp.Eval where

import DataTypes.Comp
import Functions.Comp.Desugar
import Data.Comp
import Data.Comp.Thunk hiding (eval, eval2)
import Data.Comp.Derive

-- Control.Monad.Fail import is redundant since GHC 8.8.1
#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail (MonadFail)
#endif

import Control.Monad

-- evaluation with thunks

class (Monad m, Traversable v) => EvalT e v m where
    evalTAlg :: AlgT m e v

$(derive [liftSum] [''EvalT])

evalT :: (EvalT e v m, Functor e) => Term e -> m (Term v)
evalT = nf . cata evalTAlg

instance (Monad m, Traversable v, Value :<: m :+: v) => EvalT Value v m where
    evalTAlg = inject

instance (Value :<: (m :+: v), Value :<: v, Traversable v, EqF v, MonadFail m) => EvalT Op v m where
    evalTAlg (Plus x y) = thunk $ do
                           VInt i <- whnfPr x
                           VInt j <- whnfPr y
                           return $ iVInt (i+j)
    evalTAlg (Mult x y) = thunk $ do
                           VInt i <- whnfPr x
                           VInt j <- whnfPr y
                           return $ iVInt (i*j)
    evalTAlg (If x y z) = thunk $ do 
                            VBool b <- whnfPr x
                            return $ if b then y else z
    evalTAlg (Eq x y) = thunk $ liftM iVBool $ eqT x y
    evalTAlg (Lt x y) = thunk $ do
                          VInt i <- whnfPr x
                          VInt j <- whnfPr y
                          return $ iVBool (i < j)
    evalTAlg (And x y) = thunk $ do
                           VBool b1 <- whnfPr x
                           if b1 then do
                                   VBool b2 <- whnfPr y
                                   return $ iVBool b2
                                 else return $ iVBool False
    evalTAlg (Not x) = thunk $ do
                           VBool b <- whnfPr x
                           return $ iVBool (not b)
    evalTAlg (Proj p x) = thunk $ do
                            VPair a b <- whnfPr x
                            return $ select a b
         where select x y = case p of
                              ProjLeft -> x
                              ProjRight -> y

instance (Value :<: (m :+: v), Value :<: v, Traversable v, MonadFail m) => EvalT Sugar v m where
    evalTAlg (Neg x) = thunk $ do
                         VInt i <- whnfPr x
                         return $ iVInt (-i)
    evalTAlg (Minus x y) = thunk $ do
                           VInt i <- whnfPr x
                           VInt j <- whnfPr y
                           return $ iVInt (i-j)
    evalTAlg (Gt x y) = thunk $ do
                          VInt i <- whnfPr x
                          VInt j <- whnfPr y
                          return $ iVBool (i > j)
    evalTAlg (Or x y) = thunk $ do
                           VBool b1 <- whnfPr x
                           if b1 then return $ iVBool True
                                 else do
                                   VBool b2 <- whnfPr y
                                   return $ iVBool b2
    evalTAlg (Impl x y) = thunk $ do
                           VBool b1 <- whnfPr x
                           if b1 then do
                                   VBool b2 <- whnfPr y
                                   return $ iVBool b2
                                 else return $ iVBool True
-- evaluation

class Monad m => Eval e v m where
    evalAlg :: e (Term v) -> m (Term v)

$(derive [liftSum] [''Eval])

eval :: (Traversable e, Eval e v m) => Term e -> m (Term v)
eval = cataM evalAlg

instance (Value :<: v, Monad m) => Eval Value v m where
    evalAlg = return . inject

coerceInt :: (Value :<: v, MonadFail m) => Term v -> m Int
coerceInt t = case project t of
                Just (VInt i) -> return i
                _ -> fail ""

coerceBool :: (Value :<: v, MonadFail m) => Term v -> m Bool
coerceBool t = case project t of
                Just (VBool b) -> return b
                _ -> fail ""

coercePair :: (Value :<: v, MonadFail m) => Term v -> m (Term v, Term v)
coercePair t = case project t of
                Just (VPair x y) -> return (x,y)
                _ -> fail ""

instance (Value :<: v, EqF v, MonadFail m) => Eval Op v m where
    evalAlg (Plus x y) = liftM2 (\ i j -> iVInt (i + j)) (coerceInt x) (coerceInt y)
    evalAlg (Mult x y) = liftM2 (\ i j -> iVInt (i * j)) (coerceInt x) (coerceInt y)
    evalAlg (If b x y) = liftM select (coerceBool b)
        where select b' = if b' then x else y
    evalAlg (Eq x y) = return $ iVBool (x == y)
    evalAlg (Lt x y) = liftM2 (\ i j -> iVBool (i < j)) (coerceInt x) (coerceInt y)
    evalAlg (And x y) = liftM2 (\ b c -> iVBool (b && c)) (coerceBool x) (coerceBool y)
    evalAlg (Not x) = liftM (iVBool . not) (coerceBool x)
    evalAlg (Proj p x) = liftM select (coercePair x)
        where select (x,y) = case p of 
                               ProjLeft -> x
                               ProjRight -> y

instance (Value :<: v, MonadFail m) => Eval Sugar v m where
    evalAlg (Neg x) = liftM (iVInt . negate) (coerceInt x)
    evalAlg (Minus x y) = liftM2 (\ i j -> iVInt (i - j)) (coerceInt x) (coerceInt y)
    evalAlg (Gt x y) = liftM2 (\ i j -> iVBool (i > j)) (coerceInt x) (coerceInt y)
    evalAlg (Or x y) = liftM2 (\ b c -> iVBool (b || c)) (coerceBool x) (coerceBool y)
    evalAlg (Impl x y) = liftM2 (\ b c -> iVBool (not b || c)) (coerceBool x) (coerceBool y)


-- direct evaluation

class MonadFail m => EvalDir e m where
    evalDir :: (Traversable f, EvalDir f m) => e (Term f) -> m ValueExpr

$(derive [liftSum] [''EvalDir])

evalDirect :: (Traversable e, EvalDir e m) => Term e -> m ValueExpr
evalDirect (Term x) = evalDir x

evalDirectE :: SugarExpr -> Err ValueExpr
evalDirectE = evalDirect

instance (MonadFail m) => EvalDir Value m where
    evalDir (VInt i) = return $ iVInt i
    evalDir (VBool i) = return $ iVBool i
    evalDir (VPair x y) = liftM2 iVPair (evalDirect x) (evalDirect y)


evalInt :: (Traversable e, EvalDir e m) => Term e -> m Int
evalInt t = do
  t' <- evalDirect t
  case project t' of
    Just (VInt i) -> return i
    _ -> fail ""

evalBool :: (Traversable e, EvalDir e m) => Term e -> m Bool
evalBool t = do
  t' <- evalDirect t
  case project t' of
    Just (VBool b) -> return b
    _ -> fail ""

evalPair :: (Traversable e, EvalDir e m) => Term e -> m (ValueExpr, ValueExpr)
evalPair t = do
  t' <- evalDirect t
  case project t' of
    Just (VPair x y) -> return (x,y)
    _ -> fail ""

instance (MonadFail m) => EvalDir Op m where
    evalDir (Plus x y) = liftM2 (\ i j -> iVInt (i + j)) (evalInt x) (evalInt y)
    evalDir (Mult x y) = liftM2 (\ i j -> iVInt (i * j)) (evalInt x) (evalInt y)
    evalDir (If b x y) = do 
      b' <- evalBool b
      if b' then evalDirect x else evalDirect y
    evalDir (Eq x y) = liftM iVBool $ liftM2 (==) (evalDirect x) (evalDirect y)
    evalDir (Lt x y) = liftM2 (\ i j -> iVBool (i < j)) (evalInt x) (evalInt y)
    evalDir (And x y) = liftM2 (\ b c -> iVBool (b && c)) (evalBool x) (evalBool y)
    evalDir (Not x) = liftM (iVBool . not) (evalBool x)
    evalDir (Proj p x) = liftM select (evalPair x)
        where select (x,y) = case p of 
                               ProjLeft -> x
                               ProjRight -> y

instance (MonadFail m) => EvalDir Sugar m where
    evalDir (Neg x) = liftM (iVInt . negate) (evalInt x)
    evalDir (Minus x y) = liftM2 (\ i j -> iVInt (i - j)) (evalInt x) (evalInt y)
    evalDir (Gt x y) = liftM2 (\ i j -> iVBool (i > j)) (evalInt x) (evalInt y)
    evalDir (Or x y) = liftM2 (\ b c -> iVBool (b || c)) (evalBool x) (evalBool y)
    evalDir (Impl x y) = liftM2 (\ b c -> iVBool (not b || c)) (evalBool x) (evalBool y)


-- evaluation2

class Functor e => Eval2 e v where
    eval2Alg :: e (Term v) -> Term v

$(derive [liftSum] [''Eval2])

eval2 :: (Functor e, Eval2 e v) => Term e -> Term v
eval2 = cata eval2Alg

instance (Value :<: v) => Eval2 Value v where
    eval2Alg = inject

coerceInt2 :: (Value :<: v) => Term v -> Int
coerceInt2 t = case project t of
                Just (VInt i) -> i
                _ -> undefined

coerceBool2 :: (Value :<: v) => Term v -> Bool
coerceBool2 t = case project t of
                Just (VBool b) -> b
                _ -> undefined

coercePair2 :: (Value :<: v) => Term v -> (Term v, Term v)
coercePair2 t = case project t of
                Just (VPair x y) -> (x,y)
                _ -> undefined

instance (Value :<: v, EqF v) => Eval2 Op v where
    eval2Alg (Plus x y) = (\ i j -> iVInt (i + j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (Mult x y) = (\ i j -> iVInt (i * j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (If b x y) = select (coerceBool2 b)
        where select b' = if b' then x else y
    eval2Alg (Eq x y) = iVBool (x == y)
    eval2Alg (Lt x y) = (\ i j -> iVBool (i < j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (And x y) = (\ b c -> iVBool (b && c)) (coerceBool2 x) (coerceBool2 y)
    eval2Alg (Not x) = (iVBool . not) (coerceBool2 x)
    eval2Alg (Proj p x) = select (coercePair2 x)
        where select (x,y) = case p of 
                               ProjLeft -> x
                               ProjRight -> y


instance (Value :<: v) => Eval2 Sugar v where
    eval2Alg (Neg x) = (iVInt . negate) (coerceInt2 x)
    eval2Alg (Minus x y) = (\ i j -> iVInt (i - j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (Gt x y) = (\ i j -> iVBool (i > j)) (coerceInt2 x) (coerceInt2 y)
    eval2Alg (Or x y) = (\ b c -> iVBool (b || c)) (coerceBool2 x) (coerceBool2 y)
    eval2Alg (Impl x y) = (\ b c -> iVBool (not b || c)) (coerceBool2 x) (coerceBool2 y)


-- direct evaluation 2

class EvalDir2 e where
    evalDir2 :: (EvalDir2 f) => e (Term f) -> ValueExpr

$(derive [liftSum] [''EvalDir2])

evalDirect2 :: (EvalDir2 e) => Term e -> ValueExpr
evalDirect2 (Term x) = evalDir2 x

evalDirectE2 :: SugarExpr -> ValueExpr
evalDirectE2 = evalDirect2

instance EvalDir2 Value where
    evalDir2 (VInt i) = iVInt i
    evalDir2 (VBool i) =  iVBool i
    evalDir2 (VPair x y) = iVPair (evalDirect2 x) (evalDirect2 y)


evalInt2 :: (EvalDir2 e) => Term e -> Int
evalInt2 t = case project (evalDirect2 t) of
               Just (VInt i) -> i
               _ -> error ""

evalBool2 :: (EvalDir2 e) => Term e -> Bool
evalBool2 t = case project (evalDirect2 t) of
                Just (VBool b) -> b
                _ -> error ""

evalPair2 :: (EvalDir2 e) => Term e -> (ValueExpr, ValueExpr)
evalPair2 t = case project (evalDirect2 t) of
               Just (VPair x y) -> (x,y)
               _ -> error ""

instance EvalDir2 Op where
    evalDir2 (Plus x y) = (\ i j -> iVInt (i + j)) (evalInt2 x) (evalInt2 y)
    evalDir2 (Mult x y) = (\ i j -> iVInt (i * j)) (evalInt2 x) (evalInt2 y)
    evalDir2 (If b x y) = if evalBool2 b then evalDirect2 x else evalDirect2 y
    evalDir2 (Eq x y) = iVBool $ (==) (evalDirect2 x) (evalDirect2 y)
    evalDir2 (Lt x y) = (\ i j -> iVBool (i < j)) (evalInt2 x) (evalInt2 y)
    evalDir2 (And x y) = (\ b c -> iVBool (b && c)) (evalBool2 x) (evalBool2 y)
    evalDir2 (Not x) =  (iVBool . not) (evalBool2 x)
    evalDir2 (Proj p x) =  select (evalPair2 x)
        where select (x,y) = case p of 
                               ProjLeft -> x
                               ProjRight -> y

instance EvalDir2 Sugar where
    evalDir2 (Neg x) = (iVInt . negate) (evalInt2 x)
    evalDir2 (Minus x y) = (\ i j -> iVInt (i - j)) (evalInt2 x) (evalInt2 y)
    evalDir2 (Gt x y) = (\ i j -> iVBool (i > j)) (evalInt2 x) (evalInt2 y)
    evalDir2 (Or x y) = (\ b c -> iVBool (b || c)) (evalBool2 x) (evalBool2 y)
    evalDir2 (Impl x y) = (\ b c -> iVBool (not b || c)) (evalBool2 x) (evalBool2 y)

-- desugar

desugEval :: SugarExpr -> Err ValueExpr
desugEval = eval . (desug :: SugarExpr -> Expr)

desugEvalT :: SugarExpr -> Err ValueExpr
desugEvalT = evalT . (desug :: SugarExpr -> Expr)


evalSugar :: SugarExpr -> Err ValueExpr
evalSugar = eval

evalSugarT :: SugarExpr -> Err ValueExpr
evalSugarT = evalT

desugEvalAlg  :: AlgM Err SugarSig ValueExpr
desugEvalAlg = evalAlg  `compAlgM'` (desugAlg :: Hom SugarSig ExprSig)


desugEval' :: SugarExpr -> Err ValueExpr
desugEval' = cataM desugEvalAlg

desugEvalAlgT  :: AlgT Err SugarSig Value
desugEvalAlgT = evalTAlg  `compAlg` (desugAlg :: Hom SugarSig ExprSig)

desugEvalT' :: SugarExpr -> Err ValueExpr
desugEvalT' = nf . cata desugEvalAlgT


desugEval2 :: SugarExpr -> ValueExpr
desugEval2 = eval2 . (desug :: SugarExpr -> Expr)



evalSugar2 :: SugarExpr -> ValueExpr
evalSugar2 = eval2



desugEval2Alg  :: Alg SugarSig ValueExpr
desugEval2Alg = eval2Alg  `compAlg` (desugAlg :: Hom SugarSig ExprSig)


desugEval2' :: SugarExpr -> ValueExpr
desugEval2' = cata desugEval2Alg
