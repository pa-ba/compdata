{-# LANGUAGE DataKinds, TypeFamilies, UndecidableInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.SubsumeCommon
-- Copyright   :  (c) 2014 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Shared parts of the implementation of signature subsumption for
-- both the base and the multi library.
--
--------------------------------------------------------------------------------

module Data.Comp.SubsumeCommon where

data Pos = Here | Le Pos | Ri Pos | Sum Pos Pos
data Emb = Found Pos | NotFound | Ambiguous

type family ComprPos (p :: Pos) :: Pos where
    ComprPos Here = Here
    ComprPos (Le p) = Le (ComprPos p)
    ComprPos (Ri p) = Ri (ComprPos p)
    ComprPos (Sum l r) = CombineMaybe (Sum l r) (Combine (ComprPos l) (ComprPos r))

type family CombineMaybe (p :: Pos) (p' :: Maybe Pos) where
    CombineMaybe p (Just p') = p'
    CombineMaybe p p'        = p

type family Combine (l :: Pos) (r :: Pos) :: Maybe Pos where
    Combine (Le l) (Le r) = Le' (Combine l r)
    Combine (Ri l) (Ri r) = Ri' (Combine l r)
    Combine (Le Here) (Ri Here) = Just Here
    Combine l r = Nothing

type family Ri' (p :: Maybe Pos) :: Maybe Pos where
    Ri' Nothing = Nothing
    Ri' (Just p) = Just (Ri p)

type family Le' (p :: Maybe Pos) :: Maybe Pos where
    Le' Nothing = Nothing
    Le' (Just p) = Just (Le p)

type family ComprEmb (e :: Emb) :: Emb where
    ComprEmb (Found p) = Found (ComprPos p)
    ComprEmb e = e
