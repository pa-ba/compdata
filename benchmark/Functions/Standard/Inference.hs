module Functions.Standard.Inference where

import DataTypes.Standard
import Control.Monad
import Functions.Standard.Desugar

checkOp :: (Monad m) => [VType] -> VType -> [OExpr] -> m VType
checkOp tys rety args = do 
  argsty <- mapM inferType args
  if tys == argsty
     then return rety
     else fail ""

inferType :: (Monad m) => OExpr -> m VType
inferType (OInt _) = return VTInt
inferType (OBool _) = return VTBool
inferType (OPair x y) = liftM2 VTPair (inferType x) (inferType y)
inferType (OPlus x y) = checkOp [VTInt,VTInt] VTInt [x,y]
inferType (OMult x y) = checkOp [VTInt,VTInt] VTInt [x,y]
inferType (OIf b x y) = do [bty,xty,yty] <- mapM inferType [b,x,y]
                           if (bty == VTBool) && xty == yty
                             then return xty
                             else fail ""
inferType (OLt x y) = checkOp [VTInt,VTInt] VTBool [x,y]
inferType (OEq x y) = do [xty,yty] <- mapM inferType [x,y]
                         if xty == yty
                            then return VTBool
                            else fail ""
inferType (OAnd x y) = checkOp [VTBool,VTBool] VTBool [x,y]
inferType (ONot x) = checkOp [VTBool] VTBool [x]
inferType (OProj p x) = do xty <- inferType x
                           case xty of
                             VTPair s t -> return $
                                 case p of 
                                   SProjLeft -> s
                                   SProjRight -> t
                             _ -> fail ""

desugarType :: PExpr -> Err VType
desugarType = inferType . desugar