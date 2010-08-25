{-# LANGUAGE TypeOperators, TypeSynonymInstances, GADTs, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.ALaCarte.Arbitrary
-- Copyright   :  3gERP, 2010
-- License     :  AllRightsReserved
-- Maintainer  :  Tom Hvitved, Patrick Bahr, and Morten Ib Nielsen
-- Stability   :  unknown
-- Portability :  unknown
--
--
--------------------------------------------------------------------------------

module Data.ALaCarte.Arbitrary
    ( ArbitraryF(..),
      deriveArbitraryFs,
      deriveArbitraryF
    )where

import Test.QuickCheck
import Data.ALaCarte
import Data.ALaCarte.Derive.Utils
import Data.ALaCarte.Derive.Arbitrary
import Control.Applicative

{-| This lifts instances of 'ArbitraryF' to instances of 'Arbitrary'
for the corresponding term type. -}

instance (ArbitraryF f) => Arbitrary (Term f) where
    arbitrary = Term <$> arbitraryF
    shrink (Term expr) = map Term $ shrinkF expr

instance (ArbitraryF f, Arbitrary p) => ArbitraryF (f :*: p) where
    arbitraryF' = map addP arbitraryF'
        where addP (i,gen) =  (i,(:*:) <$> gen <*> arbitrary)
    arbitraryF = (:*:) <$> arbitraryF <*> arbitrary
    shrinkF (v :*: p) = tail [v' :*: p'| v' <- v: shrinkF v, p' <- p : shrink p ]

{-|
  This lifts instances of 'ArbitraryF' to instances of 'ArbitraryF' for 
  the corresponding context functor.
-}
instance (ArbitraryF f) => ArbitraryF (Context f) where
    arbitraryF = oneof [Term <$> arbitraryF , Hole <$> arbitrary]
    shrinkF (Term expr) = map Term $ shrinkF expr
    shrinkF (Hole a) = map Hole $ shrink a


{-| This lifts instances of 'ArbitraryF' to instances of 'Arbitrary'
for the corresponding context type.  -}

instance (ArbitraryF f, Arbitrary a) => Arbitrary (Context f a) where
    arbitrary = arbitraryF
    shrink = shrinkF


{-| Instances of 'ArbitraryF' are closed under forming sums.  -}

instance (ArbitraryF f , ArbitraryF g) => ArbitraryF (f :+: g) where
    arbitraryF' = map inl arbitraryF' ++ map inr arbitraryF'
        where inl (i,gen) = (i,Inl <$> gen)
              inr (i,gen) = (i,Inr <$> gen)
    shrinkF (Inl val) = map Inl (shrinkF val)
    shrinkF (Inr val) = map Inr (shrinkF val)


$(deriveArbitraryFs $ [''Maybe,''[]] ++ tupleTypes 2 10)