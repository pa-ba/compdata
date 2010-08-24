{-# LANGUAGE TypeOperators, GADTs, TemplateHaskell, FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Equality
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
-- The equality algebra (equality on terms).
--
--------------------------------------------------------------------------------
module Data.ALaCarte.Equality
    (
     EqF(..),
     deriveEqF,
     deriveEqFs,
     match,
    ) where

import Data.ALaCarte
import Data.ALaCarte.Derive
import Language.Haskell.TH hiding (Cxt, match)
import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map


{-|
  Functor type class that provides an 'Eq' instance for the corresponding
  term type class.
-}
class EqF f where
    {-| This function is supposed to implement equality of values of
      type @f a@ modulo the equality of @a@ itself. If two functorial values
      are equal in this sense, 'eqMod' returns a 'Just' value containing a
      list of pairs consisting of corresponding components of the two
      functorial values. -}

    eqMod :: f a -> f b -> Maybe [(a,b)]

    eqAlg :: Eq a => f a -> f a -> Bool
    eqAlg x y = maybe
                False
                (all (uncurry (==)))
                (eqMod x y)

{-|
  'EqF' is propagated through sums.
-}

instance (EqF f, EqF g) => EqF (f :+: g) where
    eqMod (Inl x) (Inl y) = eqMod x y
    eqMod (Inr x) (Inr y) = eqMod x y
    eqMod _ _ = Nothing

    eqAlg (Inl x) (Inl y) = eqAlg x y
    eqAlg (Inr x) (Inr y) = eqAlg x y
    eqAlg _ _ = False

{-|
  From an 'EqF' functor an 'Eq' instance of the corresponding
  term type can be derived.
-}
instance (EqF f) => EqF (Cxt h f) where
    eqMod (Term e1) (Term e2) = liftM concat $
                                eqMod e1 e2 >>= mapM (uncurry eqMod)
    eqMod (Hole h1) (Hole h2) = Just [(h1,h2)]
    eqMod _ _ = Nothing

    eqAlg (Term e1) (Term e2) = e1 `eqAlg` e2
    eqAlg (Hole h1) (Hole h2) = h1 == h2
    eqAlg _ _ = False

instance (EqF f, Eq a)  => Eq (Cxt h f a) where
    (==) = eqAlg

{-| This is an auxiliary function for implementing 'match'. It behaves
similarly as 'match' but is oblivious to non-linearity. Therefore, the
substitution that is returned maps holes to non-empty lists of terms
(resp. contexts in general). This substitution is only a matching
substitution if all elements in each list of the substitution's range
are equal. -}

match' :: (Ord v,f :<: g, EqF f) => Context f v -> Cxt h g a -> Maybe (Map v [Cxt h g a])
match' (Hole v) t = Just $  Map.singleton v [t]
match' (Term s) t = do
  t' <- project t
  eqs <- eqMod s t'
  substs <- mapM (uncurry match') eqs
  return $ Map.unionsWith (++) substs


{-| This function takes a context @c@ as the first argument and tries
to match it against the term @t@ (or in general a context with holes
in @a@). The context @c@ matches the term @t@ if there is a /matching
substitution/ @s@ that maps holes to terms (resp. contexts in general)
such that if the holes in the context @c@ are replaced according to
the substitution @s@, the term @t@ is obtained. Note that the context
@c@ might be non-linear, i.e. has multiple holes that are
equal. According to the above definition this means that holes with
equal holes have to be instantiated by equal terms! -}

match :: (Ord v,f :<: g, EqF f, Eq (Cxt h g a))
         => Context f v -> Cxt h g a -> Maybe (Map v (Cxt h g a))
match c1 c2 = do 
  res <- match' c1 c2
  let insts = Map.elems res
  mapM_ checkEq insts
  return $ Map.map head res
    where checkEq [] = Nothing
          checkEq (c : cs)
              | all (== c) cs = Just ()
              | otherwise = Nothing
                             


{-| This function generates an instance declaration of class
'EqF' for a each of the type constructor given in the argument
list. -}

deriveEqFs :: [Name] -> Q [Dec]
deriveEqFs = liftM concat . mapM deriveEqF

{-| This function generates an instance declaration of class
'EqF' for a type constructor of any first-order kind taking at
least one argument. -}

deriveEqF :: Name -> Q [Dec]
deriveEqF fname = do
  TyConI (DataD _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let complType = foldl AppT (ConT name) (map (VarT . tyVarBndrName) (tail args))
      classType = AppT (ConT ''EqF) complType
  eqAlgDecl <- funD 'eqAlg  (eqAlgClauses constrs)
  eqModDecl <- funD 'eqMod  (eqModClauses constrs)
  return $ [InstanceD [] classType [eqModDecl, eqAlgDecl]]
      where eqAlgClauses constrs = map (genEqClause.abstractConType) constrs ++ (defEqClause constrs)
            eqModClauses constrs = map (genModClause.abstractConType) constrs ++ (defModClause constrs)
            defEqClause constrs
                | length constrs  < 2 = []
                | otherwise = [clause [wildP,wildP] (normalB [|False|]) []]
            defModClause constrs
                | length constrs  < 2 = []
                | otherwise = [clause [wildP,wildP] (normalB [|Nothing|]) []]
            genModClause (constr, n) = do 
              varNs <- newNames n "x"
              varNs' <- newNames n "y"
              let pat = ConP constr $ map VarP varNs
                  pat' = ConP constr $ map VarP varNs'
                  vars = map VarE varNs
                  vars' = map VarE varNs'
                  mkEq x y = let (x',y') = (return x,return y)
                             in [| ($x', $y')|]
                  eqs = listE $ zipWith mkEq vars vars'
              body <- [|Just $eqs|]
              return $ Clause [pat, pat'] (NormalB body) []
            genEqClause (constr, n) = do 
              varNs <- newNames n "x"
              varNs' <- newNames n "y"
              let pat = ConP constr $ map VarP varNs
                  pat' = ConP constr $ map VarP varNs'
                  vars = map VarE varNs
                  vars' = map VarE varNs'
                  mkEq x y = let (x',y') = (return x,return y)
                             in [| $x' == $y'|]
                  eqs = listE $ zipWith mkEq vars vars'
              body <- if n == 0 
                      then [|True|]
                      else [|and $eqs|]
              return $ Clause [pat, pat'] (NormalB body) []