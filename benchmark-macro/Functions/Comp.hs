module Functions.Comp where

import DataTypes.Comp

import Data.Comp
import Data.Comp.MacroAutomata

import Data.Map (Map)
import qualified Data.Map as Map


inlineTrans :: MacroTrans' Arith (Map Var) Arith
inlineTrans m (Var v) = case Map.lookup v m of
                          Nothing -> iVar v
                          Just e -> e
inlineTrans m (Let v x y) = y (Map.insert v (x m) m)
inlineTrans m f = Term $ fmap ($ m) f
