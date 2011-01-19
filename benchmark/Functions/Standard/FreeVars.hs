module Functions.Standard.FreeVars where

import DataTypes.Standard
import Data.Set (Set)
import Data.Generics.Uniplate.Data
import qualified Data.Set as Set

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