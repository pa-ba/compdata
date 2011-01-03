module Functions.Standard.Eval where

import DataTypes.Standard
import Functions.Standard.Desugar
import Control.Monad

coerceInt :: (Monad m) => SExpr -> m Int
coerceInt (SInt i) = return i
coerceInt _ = fail ""

coerceBool :: (Monad m) => SExpr -> m Bool
coerceBool (SBool b) = return b
coerceBool _ = fail ""

coercePair :: (Monad m) => SExpr -> m (SExpr,SExpr)
coercePair (SPair x y) = return (x,y)
coercePair _ = fail ""

eval :: (Monad m) => OExpr -> m SExpr
eval (OInt i) = return $ SInt i
eval (OBool b) = return $ SBool b
eval (OPair x y) = liftM2 SPair (eval x) (eval y)
eval (OPlus x y) = liftM2 (\ x y -> SInt (x + y)) (eval x >>= coerceInt) (eval y >>= coerceInt)
eval (OMult x y) = liftM2 (\ x y -> SInt (x * y)) (eval x >>= coerceInt) (eval y >>= coerceInt)
eval (OIf b x y) = eval b >>= coerceBool >>= (\b -> if b then eval x else eval y)
eval (OEq x y) = liftM2 (\ x y -> SBool (x == y)) (eval x) (eval y)
eval (OLt x y) = liftM2 (\ x y -> SBool (x < y)) (eval x >>= coerceInt) (eval y >>= coerceInt)
eval (OAnd x y) = liftM2 (\ x y -> SBool (x && y)) (eval x >>= coerceBool) (eval y >>= coerceBool)
eval (ONot x) = liftM (SBool . not)(eval x >>= coerceBool)
eval (OProj p x) = liftM select (eval x >>= coercePair)
    where select (x,y) = case p of
                           SProjLeft -> x
                           SProjRight -> y

desugarEval :: PExpr -> Err SExpr
desugarEval = eval . desugar


coerceInt2 :: SExpr -> Int
coerceInt2 (SInt i) = i
coerceInt2 _ = undefined

coerceBool2 :: SExpr -> Bool
coerceBool2 (SBool b) = b
coerceBool2 _ = undefined

coercePair2 :: SExpr -> (SExpr,SExpr)
coercePair2 (SPair x y) = (x,y)
coercePair2 _ = undefined

eval2 :: OExpr -> SExpr
eval2 (OInt i) = SInt i
eval2 (OBool b) = SBool b
eval2 (OPair x y) = SPair (eval2 x) (eval2 y)
eval2 (OPlus x y) = (\ x y -> SInt (x + y)) (coerceInt2 $ eval2 x) (coerceInt2 $ eval2 y)
eval2 (OMult x y) = (\ x y -> SInt (x * y)) (coerceInt2 $ eval2 x) (coerceInt2 $ eval2 y)
eval2 (OIf b x y) = if coerceBool2 $ eval2 b then eval2 x else eval2 y
eval2 (OEq x y) = (\ x y -> SBool (x == y)) (eval2 x) (eval2 y)
eval2 (OLt x y) = (\ x y -> SBool (x < y)) (coerceInt2 $ eval2 x) (coerceInt2 $ eval2 y)
eval2 (OAnd x y) =(\ x y -> SBool (x && y)) (coerceBool2 $ eval2 x) (coerceBool2 $ eval2 y)
eval2 (ONot x) = (SBool . not)(coerceBool2 $ eval2 x)
eval2 (OProj p x) = select (coercePair2 $ eval2 x)
    where select (x,y) = case p of
                           SProjLeft -> x
                           SProjRight -> y


desugarEval2 :: PExpr -> SExpr
desugarEval2 = eval2 . desugar