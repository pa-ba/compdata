module Functions.Standard.Desugar where

import DataTypes.Standard

-- de-sugar

desugar :: PExpr -> OExpr
desugar (PInt i) = OInt i
desugar (PBool b) = OBool b
desugar (PPair x y) = OPair (desugar x) (desugar y)
desugar (PPlus x y) = OPlus (desugar x) (desugar y)
desugar (PMult x y) = OMult (desugar x) (desugar y)
desugar (PIf b x y) = OIf (desugar b) (desugar x) (desugar y)
desugar (PEq x y) = OEq (desugar x) (desugar y)
desugar (PLt x y) = OLt (desugar x) (desugar y)
desugar (PAnd x y) = OAnd (desugar x) (desugar y)
desugar (PNot x) = ONot (desugar x)
desugar (PProj p x) = OProj p (desugar x)
desugar (PNeg x) = OInt (-1) `OMult` (desugar x)
desugar (PMinus x y) = (desugar x) `OPlus` ((OInt (-1)) `OMult` (desugar y))
desugar (PGt x y) = (desugar y) `OLt` (desugar x)
desugar (POr x y) = ONot (ONot (desugar x) `OAnd` ONot (desugar y))
desugar (PImpl x y) = ONot ((desugar x) `OAnd` ONot (desugar y))