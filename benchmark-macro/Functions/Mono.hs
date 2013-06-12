{-# LANGUAGE TypeOperators #-}

module Functions.Mono where

import DataTypes.Mono

import Data.Comp
import Data.Comp.MacroAutomata
import Data.Comp.Automata
import Data.Comp.Number

import Data.Map (Map)
import qualified Data.Map as Map

pathAnnTrans :: (Functor g, Traversable g) => DownTrans g [Int] (g :&: [Int])
pathAnnTrans q t = simpCxt (fmap (\ (Numbered (n,s)) -> s (n:q)) (number t) :&: q)


-- Inlining


inlineTrans :: MacroTrans' ArithLet (Map Var) ArithLet
inlineTrans m (Var v) = case Map.lookup v m of
                          Nothing -> iVar v
                          Just e -> e
inlineTrans m (Let v x y) = y (Map.insert v (x m) m)
inlineTrans m f = Term $ fmap ($ m) f


inlineTransExplicit :: MacroTrans ArithLet (Map Var) ArithLet
inlineTransExplicit m (Var v) = case Map.lookup v m of
                          Nothing -> iVar v
                          Just e -> Hole e
inlineTransExplicit m (Let v x y) = Hole $ y (Map.insert v (Hole $ x m') m')
                             where m' = fmap Hole m
inlineTransExplicit m (Add x y) = iAdd (Hole $ x m') (Hole $ y m')
                             where m' = fmap Hole m
inlineTransExplicit m (Mult x y) = iMult (Hole $ x m') (Hole $ y m')
                             where m' = fmap Hole m
inlineTransExplicit m (Sub x y) = iSub (Hole $ x m') (Hole $ y m')
                             where m' = fmap Hole m
inlineTransExplicit _ (Val n) = iVal n


inlineAnnFuse :: Term ArithLet -> Term (ArithLet :&: [Int])
inlineAnnFuse t = runMacroTrans (compMacroDown (propAnnMacro inlineTransExplicit) pathAnnTrans)
                (Map.empty :&: []) t

inlineAnnImpFuse :: Term ArithLet -> Term (ArithLet :&: [Int])
inlineAnnImpFuse t = runMacroTrans (compMacroDown (propAnnMacro $ mkMacroTrans inlineTrans)
                                    pathAnnTrans) (Map.empty :&: []) t

inlineAnnSeq  :: Term ArithLet -> Term (ArithLet :&: [Int])
inlineAnnSeq t = runMacroTrans (propAnnMacro inlineTransExplicit) Map.empty 
                  (runDownTrans pathAnnTrans [] t)

inlineAnnImpSeq  :: Term ArithLet -> Term (ArithLet :&: [Int])
inlineAnnImpSeq t = runMacroTrans (propAnnMacro $ mkMacroTrans inlineTrans) Map.empty 
                  (runDownTrans pathAnnTrans [] t)

annInlineFuse :: Term ArithLet -> Term (ArithLet :&: [Int])
annInlineFuse t = runMacroTrans (compDownMacro pathAnnTrans inlineTransExplicit) 
                  (Map.empty :^: []) t

annInlineImpFuse :: Term ArithLet -> Term (ArithLet :&: [Int])
annInlineImpFuse t = runMacroTrans (compDownMacro pathAnnTrans (mkMacroTrans inlineTrans)) 
                  (Map.empty :^: []) t

annInlineSeq :: Term ArithLet -> Term (ArithLet :&: [Int])
annInlineSeq t = runDownTrans pathAnnTrans [] (runMacroTrans inlineTransExplicit Map.empty t)

annInlineImpSeq :: Term ArithLet -> Term (ArithLet :&: [Int])
annInlineImpSeq t = runDownTrans pathAnnTrans [] (runMacroTrans (mkMacroTrans inlineTrans) Map.empty t)


-- Code generator

compTrans :: MacroTransId' ArithExc Code
compTrans q (Val' n) = iPUSH n q
compTrans q (Add' x y) = x $ y $ iADD q
compTrans _ Throw = iTHROW
compTrans q (Catch x h) = iMARK (h q) (x $ iUNMARK q)


compAnnFuse :: Term ArithExc -> Term (Code :&: [Int])
compAnnFuse t = runMacroTrans (compMacroDown (propAnnMacro $ fromMacroTransId' compTrans) pathAnnTrans ) (I (ann [] iNIL) :&: [])  t

compAnnSeq :: Term ArithExc -> Term (Code :&: [Int])
compAnnSeq t = runMacroTrans (propAnnMacro $ fromMacroTransId' compTrans) (I (ann [] iNIL))
               (runDownTrans pathAnnTrans [] t)

annCompFuse :: Term ArithExc -> Term (Code :&: [Int])
annCompFuse t = runMacroTrans (compDownMacro pathAnnTrans (fromMacroTransId' compTrans)) 
                (I (`ann` iNIL) :^: []) t

annCompSeq :: Term ArithExc -> Term (Code :&: [Int])
annCompSeq t = runDownTrans pathAnnTrans [] (runMacroTrans (fromMacroTransId' compTrans)
                (I iNIL) t)