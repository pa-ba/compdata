module Transformations where

import DataTypes
import Data.Comp


toBaseExp :: Term Value -> BaseExp
toBaseExp = algHom toBaseExpAlg
    where toBaseExpAlg (VInt i) = BInt i
          toBaseExpAlg (VBool b) = BBool b
          toBaseExpAlg (VString s) = BString s
          toBaseExpAlg (VDateTime d) = BDateTime d
          toBaseExpAlg (VDuration d) = BDuration d
          toBaseExpAlg (VDouble d) = BDouble d
          toBaseExpAlg (VRecord r) = BRecord r
          toBaseExpAlg (VList l) = BList l

toRepExp :: Term Value -> RepExp
toRepExp = algHom toRepExpAlg
    where toRepExpAlg (VInt i) = RInt i
          toRepExpAlg (VBool b) = RBool b
          toRepExpAlg (VString s) = RString s
          toRepExpAlg (VDateTime d) = RDateTime d
          toRepExpAlg (VDuration d) = RDuration d
          toRepExpAlg (VDouble d) = RDouble d
          toRepExpAlg (VRecord r) = RRecord r
          toRepExpAlg (VList l) = RList l
