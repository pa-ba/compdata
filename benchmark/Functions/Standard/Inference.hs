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


checkOpP :: [VType] -> VType -> [PExpr] -> Err VType
checkOpP tys rety args = do 
  argsty <- mapM typeSugar args
  if tys == argsty
     then return rety
     else fail ""

--typeSugar :: (Monad m) => PExpr -> m VType
typeSugar :: PExpr -> Err VType
typeSugar (PInt _) = return VTInt
typeSugar (PBool _) = return VTBool
typeSugar (PPair x y) = liftM2 VTPair (typeSugar x) (typeSugar y)
typeSugar (PPlus x y) = checkOpP [VTInt,VTInt] VTInt [x,y]
typeSugar (PMult x y) = checkOpP [VTInt,VTInt] VTInt [x,y]
typeSugar (PIf b x y) = do [bty,xty,yty] <- mapM typeSugar [b,x,y]
                           if (bty == VTBool) && xty == yty
                             then return xty
                             else fail ""
typeSugar (PLt x y) = checkOpP [VTInt,VTInt] VTBool [x,y]
typeSugar (PEq x y) = do [xty,yty] <- mapM typeSugar [x,y]
                         if xty == yty
                            then return VTBool
                            else fail ""
typeSugar (PAnd x y) = checkOpP [VTBool,VTBool] VTBool [x,y]
typeSugar (PNot x) = checkOpP [VTBool] VTBool [x]
typeSugar (PProj p x) = do xty <- typeSugar x
                           case xty of
                             VTPair s t -> return $
                                 case p of 
                                   SProjLeft -> s
                                   SProjRight -> t
                             _ -> fail ""
typeSugar (PNeg x) = checkOpP [VTInt] VTInt [x]
typeSugar (PMinus x y) = checkOpP [VTInt,VTInt] VTInt [x,y]
typeSugar (PGt x y) = checkOpP [VTInt,VTInt] VTBool [x,y]
typeSugar (POr x y) = checkOpP [VTBool,VTBool] VTBool [x,y]
typeSugar (PImpl x y) = checkOpP [VTBool,VTBool] VTBool [x,y]

desugType :: PExpr -> Err VType
desugType = inferType . desug

-- non-monadic

checkOp2 :: [VType] -> VType -> [OExpr] -> VType
checkOp2 tys rety args = 
  if tys == map inferType2 args
     then rety
     else error ""

inferType2 :: OExpr -> VType
inferType2 (OInt _) = VTInt
inferType2 (OBool _) = VTBool
inferType2 (OPair x y) = VTPair (inferType2 x) (inferType2 y)
inferType2 (OPlus x y) = checkOp2 [VTInt,VTInt] VTInt [x,y]
inferType2 (OMult x y) = checkOp2 [VTInt,VTInt] VTInt [x,y]
inferType2 (OIf b x y) =  let [bty,xty,yty] = map inferType2 [b,x,y]
                         in if (bty == VTBool) && xty == yty
                             then xty
                             else error ""
inferType2 (OLt x y) = checkOp2 [VTInt,VTInt] VTBool [x,y]
inferType2 (OEq x y) = let [xty,yty] = map inferType2 [x,y]
                      in if xty == yty
                            then VTBool
                            else error ""
inferType2 (OAnd x y) = checkOp2 [VTBool,VTBool] VTBool [x,y]
inferType2 (ONot x) = checkOp2 [VTBool] VTBool [x]
inferType2 (OProj p x) = let xty = inferType2 x
                        in case xty of
                             VTPair s t -> 
                                 case p of 
                                   SProjLeft -> s
                                   SProjRight -> t
                             _ -> error ""


checkOpP2 :: [VType] -> VType -> [PExpr] -> VType
checkOpP2 tys rety args = 
  if tys == map typeSugar2 args
     then rety
     else error ""

--typeSugar :: (Monad m) => PExpr -> m VType
typeSugar2 :: PExpr -> VType
typeSugar2 (PInt _) = VTInt
typeSugar2 (PBool _) = VTBool
typeSugar2 (PPair x y) = VTPair (typeSugar2 x) (typeSugar2 y)
typeSugar2 (PPlus x y) = checkOpP2 [VTInt,VTInt] VTInt [x,y]
typeSugar2 (PMult x y) = checkOpP2 [VTInt,VTInt] VTInt [x,y]
typeSugar2 (PIf b x y) = let [bty,xty,yty] = map typeSugar2 [b,x,y]
                        in if (bty == VTBool) && xty == yty
                             then xty
                             else error ""
typeSugar2 (PLt x y) = checkOpP2 [VTInt,VTInt] VTBool [x,y]
typeSugar2 (PEq x y) = let [xty,yty] = map typeSugar2 [x,y]
                      in if xty == yty
                            then VTBool
                            else error ""
typeSugar2 (PAnd x y) = checkOpP2 [VTBool,VTBool] VTBool [x,y]
typeSugar2 (PNot x) = checkOpP2 [VTBool] VTBool [x]
typeSugar2 (PProj p x) = let xty = typeSugar2 x
                        in case xty of
                             VTPair s t -> 
                                 case p of 
                                   SProjLeft -> s
                                   SProjRight -> t
                             _ -> error ""
typeSugar2 (PNeg x) = checkOpP2 [VTInt] VTInt [x]
typeSugar2 (PMinus x y) = checkOpP2 [VTInt,VTInt] VTInt [x,y]
typeSugar2 (PGt x y) = checkOpP2 [VTInt,VTInt] VTBool [x,y]
typeSugar2 (POr x y) = checkOpP2 [VTBool,VTBool] VTBool [x,y]
typeSugar2 (PImpl x y) = checkOpP2 [VTBool,VTBool] VTBool [x,y]

desugType2 :: PExpr -> VType
desugType2 = inferType2 . desug