module Functions.Standard.FreeVars where

import DataTypes.Standard
import Data.Generics.PlateDirect

instance Uniplate PExpr where
    uniplate (PInt x) = plate PInt |- x
    uniplate (PBool x) = plate PBool |- x
    uniplate (PPair x y) = plate PPair |* x |* y
    uniplate (PMult x y) = plate PMult |* x |* y
    uniplate (PPlus x y) = plate PPlus |* x |* y
    uniplate (PIf x y z) = plate PIf |* x |* y |* z
    uniplate (PEq x y) = plate PEq |* x |* y
    uniplate (PLt x y) = plate PLt |* x |* y
    uniplate (PAnd x y) = plate PAnd |* x |* y
    uniplate (PNot x) = plate PNot |* x
    uniplate (PProj x y) = plate PProj |- x |* y
    uniplate (PNeg x) = plate PNeg |* x
    uniplate (PMinus x y) = plate PMinus |* x |* y
    uniplate (PGt x y) = plate PGt |* x |* y
    uniplate (POr x y) = plate POr |* x |* y
    uniplate (PImpl x y) = plate PImpl |* x |* y


contVar :: Int -> PExpr -> Bool
contVar v e = 
    case e of
      PInt i -> i == v
      PBool{} -> False
      PPair x y -> re x || re y
      PPlus x y -> re x || re y
      PMult x y -> re x || re y
      PIf x y z -> re x || re y || re z
      PEq x y -> re x || re y
      PLt x y -> re x || re y
      PAnd x y -> re x || re y
      PNot x -> re x
      PProj _ x -> re x
      PNeg x -> re x
      PMinus x y -> re x || re y
      PGt x y -> re x || re y
      POr x y -> re x || re y
      PImpl x y -> re x || re y
    where re = contVar v

freeVars :: PExpr -> [Int]
freeVars e = 
    case e of
      PInt i -> [i]
      PBool{} -> []
      PPair x y -> re2 x y
      PPlus x y -> re2 x y
      PMult x y -> re2 x y
      PIf x y z -> re3 x y z
      PEq x y -> re2 x y
      PLt x y -> re2 x y
      PAnd x y -> re2 x y
      PNot x -> re x
      PProj _ x -> re x
      PNeg x -> re x
      PMinus x y -> re2 x y
      PGt x y -> re2 x y
      POr x y -> re2 x y
      PImpl x y -> re2 x y
    where re = freeVars
          re2 x y = re x ++ re y
          re3 x y z = re x ++ re y ++ re z

contVarGen :: Int -> PExpr -> Bool
contVarGen v e = elem v [ j | (PInt j) <- universe e]

freeVarsGen :: PExpr -> [Int]
freeVarsGen e = [ j | (PInt j) <- universe e]