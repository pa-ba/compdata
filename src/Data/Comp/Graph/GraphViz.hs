{-# LANGUAGE ScopedTypeVariables, ParallelListComp, FlexibleInstances #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Graph.GraphViz
-- Copyright   :  (c) 2012 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.Graph.GraphViz 
    ( previewGraph ) where

import Data.Comp.Graph
import Data.Comp.Number
import Data.Comp.Show
import Data.Foldable (toList)

import Data.Graph.Inductive.Graph hiding (Graph)

import qualified Data.IntMap as IntMap

import Data.Graph.Inductive.PatriciaTree

import Data.GraphViz hiding (graphEdges)

toFGL :: forall  f . Traversable f => Graph f -> Gr (f Int) Int
toFGL g = mkGraph nodes edges
    where runNodes :: [LNode (f Int)] -> Int -> (f Int) -> [LNode (f Int)]
          runNodes ns k e = (k, numberFrom 0 e) : ns
          nodes :: [LNode (f Int)]
          nodes = IntMap.foldlWithKey runNodes [] (graphEdges g)
          edges = IntMap.foldlWithKey runEdges [] (graphEdges g)
          runEdges :: [LEdge Int] -> Int -> (f Int) -> [LEdge Int]
          runEdges es k e = [(k, t, l) | t  <- toList e | l <- [0..]] ++ es

previewGraph :: (Traversable f, ShowF f) => Graph f -> IO ()
previewGraph g = preview (toFGL g)

instance (ShowF f, Functor f) => Labellable (f Int) where
    toLabelValue x = toLabelValue $ showF (fmap show x)