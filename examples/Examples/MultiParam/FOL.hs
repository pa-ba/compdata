{-# LANGUAGE TemplateHaskell, TypeOperators, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, GADTs, KindSignatures,
  OverlappingInstances, TypeSynonymInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.FOL
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- First-Order Logic à la Carte
--
-- This example illustrates how to implement First-Order Logic à la Carte
-- (Knowles, The Monad.Reader Issue 11, '08) using Generalised Parametric
-- Compositional Data Types.
--
-- Rather than having a fixed domain @Term@ for binders, a la Knowles, our
-- encoding uses a mutually recursive data structure for terms and formulae.
-- This enables variables to be introduced only when they are actually needed
-- in the term language, i.e. in stage 5.
--
--------------------------------------------------------------------------------

module Examples.MultiParam.FOL where

import Data.Comp.MultiParam hiding (Const)
import Data.Comp.MultiParam.Show ()
import Data.Comp.MultiParam.Derive
import Data.Comp.MultiParam.FreshM (genVar)
import Data.List (intersperse)
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader

-- Phantom types indicating whether a (recursive) term is a formula or a term
data TFormula
data TTerm

-- Terms
data Const :: (* -> *) -> (* -> *) -> * -> * where
              Const :: String -> [e TTerm] -> Const a e TTerm
data Var :: (* -> *) -> (* -> *) -> * -> * where
            Var :: String -> Var a e TTerm

-- Formulae
data TT :: (* -> *) -> (* -> *) -> * -> * where
           TT :: TT a e TFormula
data FF :: (* -> *) -> (* -> *) -> * -> * where
           FF :: FF a e TFormula
data Atom :: (* -> *) -> (* -> *) -> * -> * where
             Atom :: String -> [e TTerm] -> Atom a e TFormula
data NAtom :: (* -> *) -> (* -> *) -> * -> * where
              NAtom :: String -> [e TTerm] -> NAtom a e TFormula
data Not :: (* -> *) -> (* -> *) -> * -> * where
            Not :: e TFormula -> Not a e TFormula
data Or :: (* -> *) -> (* -> *) -> * -> * where
           Or :: e TFormula -> e TFormula -> Or a e TFormula
data And :: (* -> *) -> (* -> *) -> * -> * where
            And :: e TFormula -> e TFormula -> And a e TFormula
data Impl :: (* -> *) -> (* -> *) -> * -> * where
             Impl :: e TFormula -> e TFormula -> Impl a e TFormula
data Exists :: (* -> *) -> (* -> *) -> * -> * where
               Exists :: (a TTerm -> e TFormula) -> Exists a e TFormula
data Forall :: (* -> *) -> (* -> *) -> * -> * where
               Forall :: (a TTerm -> e TFormula) -> Forall a e TFormula

-- Derive boilerplate code using Template Haskell
$(derive [instanceHDifunctor, smartConstructors]
         [''Const, ''Var, ''Atom, ''NAtom,
          ''Not, ''Or, ''And, ''Impl, ''Exists, ''Forall])
$(derive [instanceHDifunctor] [''TT, ''FF])

-- TODO: Fix deriving mechanism
iTT :: (TT :<: f) => Cxt h f a b TFormula
iTT = inject TT

iFF :: (FF :<: f) => Cxt h f a b TFormula
iFF = inject FF

--------------------------------------------------------------------------------
-- Pretty printing of terms and formulae
--------------------------------------------------------------------------------

instance ShowHD Const where
    showHD (Const f t) = do
      ts <- mapM pshow t
      return $ f ++ "(" ++ concat (intersperse ", " ts) ++ ")"

instance ShowHD Var where
    showHD (Var x) = return x

instance ShowHD TT where
    showHD TT = return "true"

instance ShowHD FF where
    showHD FF = return "false"

instance ShowHD Atom where
    showHD (Atom p t) = do
      ts <- mapM pshow t
      return $ p ++ "(" ++ concat (intersperse ", " ts) ++ ")"

instance ShowHD NAtom where
    showHD (NAtom p t) = do
      ts <- mapM pshow t
      return $ "not " ++ p ++ "(" ++ concat (intersperse ", " ts) ++ ")"

instance ShowHD Not where
    showHD (Not f) = liftM (\x -> "not (" ++ x ++ ")") (pshow f)

instance ShowHD Or where
    showHD (Or f1 f2) =
        liftM2 (\x y -> "(" ++ x ++ ") or (" ++ y ++ ")") (pshow f1) (pshow f2)

instance ShowHD And where
    showHD (And f1 f2) =
        liftM2 (\x y -> "(" ++ x ++ ") and (" ++ y ++ ")") (pshow f1) (pshow f2)

instance ShowHD Impl where
    showHD (Impl f1 f2) =
        liftM2 (\x y -> "(" ++ x ++ ") -> (" ++ y ++ ")") (pshow f1) (pshow f2)

instance ShowHD Exists where
    showHD (Exists f) = do x <- genVar
                           x' <- pshow x
                           b <- pshow $ f x
                           return $ "exists " ++ x' ++ ". " ++ b

instance ShowHD Forall where
    showHD (Forall f) = do x <- genVar
                           x' <- pshow x
                           b <- pshow $ f x
                           return $ "forall " ++ x' ++ ". " ++ b

--------------------------------------------------------------------------------
-- Stage 0
--------------------------------------------------------------------------------

type Input = Const :+: TT :+: FF :+: Atom :+: Not :+: Or :+: And :+:
             Impl :+: Exists :+: Forall

foodFact :: Term Input TFormula
foodFact =
    (iExists $ \p -> iAtom "Person" [Place p] `iAnd`
                     (iForall $ \f -> iAtom "Food" [Place f] `iImpl`
                                      iAtom "Eats" [Place p,Place f])) `iImpl`
    iNot (iExists $ \f -> iAtom "Food" [Place f] `iAnd`
                          iNot (iExists $ \p -> iAtom "Person" [Place p] `iAnd`
                                                iAtom "Eats" [Place p,Place f]))

--------------------------------------------------------------------------------
-- Stage 1
--------------------------------------------------------------------------------

type Stage1 = Const :+: TT :+: FF :+: Atom :+: Not :+: Or :+: And :+:
              Exists :+: Forall

class ElimImp f where
    elimImpHom :: TermHom f Stage1

$(derive [liftSum] [''ElimImp])

instance (f :<: Stage1) => ElimImp f where
    elimImpHom = simpCxt . inj

instance ElimImp Impl where
    elimImpHom (Impl f1 f2) = iNot (Hole f1) `iOr` (Hole f2)

elimImp :: Term Input :-> Term Stage1
elimImp = appTermHom elimImpHom

foodFact1 :: Term Stage1 TFormula
foodFact1 = elimImp foodFact

--------------------------------------------------------------------------------
-- Stage 2
--------------------------------------------------------------------------------

type Stage2 = Const :+: TT :+: FF :+: Atom :+: NAtom :+: Or :+: And :+:
              Exists :+: Forall

class Dualize f where
    dualizeHom :: TermHom f Stage2

$(derive [liftSum] [''Dualize])

instance Dualize Const where
    dualizeHom (Const f t) = iConst f $ map Hole t

instance Dualize TT where
    dualizeHom TT = iFF

instance Dualize FF where
    dualizeHom FF = iTT

instance Dualize Atom where
    dualizeHom (Atom p t) = iNAtom p $ map Hole t

instance Dualize NAtom where
    dualizeHom (NAtom p t) = iAtom p $ map Hole t

instance Dualize Or where
    dualizeHom (Or f1 f2) = Hole f1 `iAnd` Hole f2

instance Dualize And where
    dualizeHom (And f1 f2) = Hole f1 `iOr` Hole f2

instance Dualize Exists where
    dualizeHom (Exists f) = iForall (Hole . f)

instance Dualize Forall where
    dualizeHom (Forall f) = iExists (Hole . f)

dualize :: Term Stage2 :-> Term Stage2
dualize = appTermHom dualizeHom

class PushNot f where
    pushNotAlg :: Alg f (Term Stage2)

$(derive [liftSum] [''PushNot])

instance PushNot Const where
    pushNotAlg (Const f t) = iConst f t

instance PushNot TT where
    pushNotAlg TT = iTT

instance PushNot FF where
    pushNotAlg FF = iFF

instance PushNot Atom where
    pushNotAlg (Atom p t) = iAtom p t

instance PushNot Not where
    pushNotAlg (Not f) = dualize f

instance PushNot Or where
    pushNotAlg (Or f1 f2) = f1 `iOr` f2

instance PushNot And where
    pushNotAlg (And f1 f2) = f1 `iAnd` f2

instance PushNot Exists where
    pushNotAlg (Exists f) = iExists (f . Place)

instance PushNot Forall where
    pushNotAlg (Forall f) = iForall (f . Place)

pushNotInwards :: Term Stage1 :-> Term Stage2
pushNotInwards = cata pushNotAlg

foodFact2 :: Term Stage2 TFormula
foodFact2 = pushNotInwards foodFact1

--------------------------------------------------------------------------------
-- Stage 4
--------------------------------------------------------------------------------

type Stage4 = Const :+: TT :+: FF :+: Atom :+: NAtom :+: Or :+: And :+: Forall

type Unique = Int
data UniqueSupply = UniqueSupply Unique UniqueSupply UniqueSupply

initialUniqueSupply :: UniqueSupply
initialUniqueSupply = genSupply 1
    where genSupply n = UniqueSupply n (genSupply (2 * n))
                                       (genSupply (2 * n + 1))

splitUniqueSupply :: UniqueSupply -> (UniqueSupply, UniqueSupply)
splitUniqueSupply (UniqueSupply	_ l r) = (l,r)

getUnique :: UniqueSupply -> (Unique, UniqueSupply)
getUnique (UniqueSupply n l _) = (n,l)

type Supply = State UniqueSupply
type S = ReaderT [Term Stage4 TTerm] Supply

evalS :: S a -> [Term Stage4 TTerm] -> UniqueSupply -> a
evalS m env s = evalState (runReaderT m env) s

fresh :: S Int
fresh = do supply <- get
           let (uniq,rest) = getUnique supply
           put rest
           return uniq

freshes :: S UniqueSupply
freshes = do supply <- get
             let (l,r) = splitUniqueSupply supply
             put r
             return l

class Skolem f where
    skolemAlg :: AlgM' S f (Term Stage4)

$(derive [liftSum] [''Skolem])

instance Skolem Const where
    skolemAlg (Const f t) = liftM (iConst f) $ mapM getCompose t

instance Skolem TT where
    skolemAlg TT = return iTT

instance Skolem FF where
    skolemAlg FF = return iFF

instance Skolem Atom where
    skolemAlg (Atom p t) = liftM (iAtom p) $ mapM getCompose t

instance Skolem NAtom where
    skolemAlg (NAtom p t) = liftM (iNAtom p) $ mapM getCompose t

instance Skolem Or where
    skolemAlg (Or f1 f2) = liftM2 iOr (getCompose f1) (getCompose f2)

instance Skolem And where
    skolemAlg (And f1 f2) = liftM2 iAnd (getCompose f1) (getCompose f2)

instance Skolem Forall where
    skolemAlg (Forall f) = do
      supply <- freshes
      xs <- ask
      return $ iForall $ \x -> evalS (getCompose $ f (Place x))
                                     (Place x : xs)
                                     supply

instance Skolem Exists where
    skolemAlg (Exists f) = do uniq <- fresh
                              xs <- ask
                              getCompose $ f (iConst ("Skol" ++ show uniq) xs)

skolemize :: Term Stage2 :-> Term Stage4
skolemize f = evalState (runReaderT (cataM' skolemAlg f) []) initialUniqueSupply

foodFact4 :: Term Stage4 TFormula
foodFact4 = skolemize foodFact2

--------------------------------------------------------------------------------
-- Stage 5
--------------------------------------------------------------------------------

type Stage5 = Const :+: Var :+: TT :+: FF :+: Atom :+: NAtom :+: Or :+: And

class Prenex f where
    prenexAlg :: AlgM' S f (Term Stage5)

$(derive [liftSum] [''Prenex])

instance Prenex Const where
    prenexAlg (Const f t) = liftM (iConst f) $ mapM getCompose t

instance Prenex TT where
    prenexAlg TT = return iTT

instance Prenex FF where
    prenexAlg FF = return iFF

instance Prenex Atom where
    prenexAlg (Atom p t) = liftM (iAtom p) $ mapM getCompose t

instance Prenex NAtom where
    prenexAlg (NAtom p t) = liftM (iNAtom p) $ mapM getCompose t

instance Prenex Or where
    prenexAlg (Or f1 f2) = liftM2 iOr (getCompose f1) (getCompose f2)

instance Prenex And where
    prenexAlg (And f1 f2) = liftM2 iAnd (getCompose f1) (getCompose f2)

instance Prenex Forall where
    prenexAlg (Forall f) = do uniq <- fresh
                              getCompose $ f (iVar ("x" ++ show uniq))

prenex :: Term Stage4 :-> Term Stage5
prenex f = evalState (runReaderT (cataM' prenexAlg f) []) initialUniqueSupply

foodFact5 :: Term Stage5 TFormula
foodFact5 = prenex foodFact4

--------------------------------------------------------------------------------
-- Stage 6
--------------------------------------------------------------------------------

type Literal = Term (Const :+: Var :+: Atom :+: NAtom)
newtype Clause i = Clause {unClause :: [Literal i]} -- implicit disjunction
newtype CNF i = CNF {unCNF :: [Clause i]} -- implicit conjunction

instance Show (Clause i) where
    show c = concat $ intersperse " or " $ map show $ unClause c

instance Show (CNF i) where
    show c = concat $ intersperse "\n" $ map show $ unCNF c

class ToCNF f where
    cnfAlg :: Alg f CNF

$(derive [liftSum] [''ToCNF])

instance ToCNF Const where
    cnfAlg (Const f t) = CNF [Clause [iConst f (map (head . unClause . head . unCNF) t)]]

instance ToCNF Var where
    cnfAlg (Var x) = CNF [Clause [iVar x]]

instance ToCNF TT where
    cnfAlg TT = CNF []

instance ToCNF FF where
    cnfAlg FF = CNF [Clause []]

instance ToCNF Atom where
    cnfAlg (Atom p t) = CNF [Clause [iAtom p (map (head . unClause . head . unCNF) t)]]

instance ToCNF NAtom where
    cnfAlg (NAtom p t) = CNF [Clause [iNAtom p (map (head . unClause . head . unCNF) t)]]

instance ToCNF And where
    cnfAlg (And f1 f2) = CNF $ unCNF f1 ++ unCNF f2

instance ToCNF Or where
    cnfAlg (Or f1 f2) = CNF [Clause (x ++ y) | Clause x <- unCNF f1, Clause y <- unCNF f2]

cnf :: Term Stage5 :-> CNF
cnf = cata cnfAlg

foodFact6 :: CNF TFormula
foodFact6 = cnf foodFact5

--------------------------------------------------------------------------------
-- Stage 7
--------------------------------------------------------------------------------

type T = Const :+: Var :+: Atom :+: NAtom
newtype IClause i = IClause ([Term T i], -- implicit conjunction
                             [Term T i]) -- implicit disjunction
newtype INF i = INF [IClause i] -- implicit conjunction

instance Show (IClause i) where
    show (IClause (cs,ds)) =
        let cs' = concat $ intersperse " and " $ map show cs
            ds' = concat $ intersperse " or " $ map show ds
        in "(" ++ cs' ++ ") -> (" ++ ds' ++ ")"

instance Show (INF i) where
    show (INF fs) = concat $ intersperse "\n" $ map show fs

inf :: CNF TFormula -> INF TFormula
inf (CNF f) = INF $ map (toImpl . unClause) f
    where toImpl :: [Literal TFormula] -> IClause TFormula
          toImpl disj = IClause ([iAtom p t | NAtom p t <- mapMaybe proj1 disj],
                                 [inject t | t <- mapMaybe proj2 disj])
          proj1 :: NatM Maybe (Term T) (NAtom Any (Term T))
          proj1 = project
          proj2 :: NatM Maybe (Term T) (Atom Any (Term T))
          proj2 = project

foodFact7 :: INF TFormula
foodFact7 = inf foodFact6