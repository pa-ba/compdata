module Functions.Standard.Desugar where

import DataTypes.Standard

-- de-sugar

desug :: PExpr -> OExpr
desug (PInt i) = OInt i
desug (PBool b) = OBool b
desug (PPair x y) = OPair (desug x) (desug y)
desug (PPlus x y) = OPlus (desug x) (desug y)
desug (PMult x y) = OMult (desug x) (desug y)
desug (PIf b x y) = OIf (desug b) (desug x) (desug y)
desug (PEq x y) = OEq (desug x) (desug y)
desug (PLt x y) = OLt (desug x) (desug y)
desug (PAnd x y) = OAnd (desug x) (desug y)
desug (PNot x) = ONot (desug x)
desug (PProj p x) = OProj p (desug x)
desug (PNeg x) = OInt (-1) `OMult` (desug x)
desug (PMinus x y) = (desug x) `OPlus` ((OInt (-1)) `OMult` (desug y))
desug (PGt x y) = (desug y) `OLt` (desug x)
desug (POr x y) = ONot (ONot (desug x) `OAnd` ONot (desug y))
desug (PImpl x y) = ONot ((desug x) `OAnd` ONot (desug y))