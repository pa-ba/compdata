{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances,
FlexibleInstances, TypeFamilies, GADTs, TypeOperators, BangPatterns #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Graph
-- Copyright   :  (c) 2012 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

module Data.Comp.Graph
    ( Graph
    , termTree
    , unravelGraph
    , appGraphCxt
    , reifyGraph
    , graphCata
    , graphEdges
    ) where

import Data.Comp.Term
import Data.Comp.Algebra

import System.Mem.StableName

import Safe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Control.Monad.State hiding (mapM)
import Control.Monad.Writer hiding (mapM)
import Prelude hiding (mapM)
import Data.Traversable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy (HashMap)

type Node = Int

-- | This type represents graphs over a given signature with a
-- distinguished root node. Such graphs, also known as term graphs,
-- represent terms. This representation is given by the unravelling
-- operation (cf. 'unravelGraph').
data Graph f = Graph { _root :: Node
                     , _eqs :: IntMap (f Node)
                     , _next :: Node }

data GraphCxt f a = GraphCxt { _graph :: Graph f
                             , _holes :: IntMap a }

-- The data type 'Graph' is made abstract. Functions that construct
-- graphs are expected to maintain the invariant that the
-- distinguished root node as well as each target node of the edges is
-- defined in the graph, i.e. it is an element of the domain of the
-- IntMap.

-- data GraphI f = forall n . (Ord n) => GraphI { root :: n
--                                              , edge :: n -> f n}
             
-- graph :: Graph f -> GraphI f
-- graph (Graph n imap _) = GraphI {root = n, edge = (`lookupNode` imap)}

-- data GraphCxtI f a = forall n . (Ord n) => GraphCxtI { cxtRoot :: n
--                                                      , cxtEdge :: n -> Either (f n) a}

-- graphCxt :: GraphCxt f h -> GraphCxtI f h
-- graphCxt (GraphCxt (Graph n imap _) holes) = 
--     GraphCxtI { cxtRoot = n
--               , cxtEdge = \n -> case IntMap.lookup n imap of
--                                   Just c -> Left c
--                                   _      -> case IntMap.lookup n holes of
--                                               Just h -> Right h
--                                               _      -> error "edge leading to an undefined node" }

graphEdges :: Graph f -> IntMap (f Node)
graphEdges = _eqs

type AppT f = (Node, IntMap Node, [(Node, f Node)])

appGraphCxt :: forall f . (Functor f) => GraphCxt f (Graph f) -> Graph f
appGraphCxt (GraphCxt (Graph root eqs nx) (holes)) = Graph root' eqs' nx'
    where run :: Node -> Graph f -> AppT f -> AppT f
          run n (Graph r e nx) (next,rename,neweqs) = 
              (next+nx,
               IntMap.insert n (r+next) rename,
               [(left + next, fmap (+next) right) | (left , right ) <- IntMap.toList e] ++ neweqs)
          init :: AppT g
          init = (nx,IntMap.empty, [])
          (nx',rename,new)= IntMap.foldrWithKey run init holes
          renameFun :: Node -> Node
          renameFun n = IntMap.findWithDefault n n rename
          eqs' = foldl (\ m (k,v) -> IntMap.insert k v m) (IntMap.map (fmap renameFun) eqs) new
          root' = renameFun root

-- | This function turns a term into a graph without (explicit)
-- sharing, i.e. a tree. The following property holds for 'termTree'
-- and 'unravelGraph':
-- 
-- @
-- unravelGraph (termTree x) == x
-- @
termTree :: Traversable f => Term f -> Graph f
termTree t = Graph 0 imap nx
    where (imap,nx) = runState (liftM snd $ runWriterT $ build t) 0
          build :: Traversable f => Term f -> WriterT (IntMap (f Node)) (State Node) Node
          build (Term t) = do n <- liftM (+1) get
                              put n
                              res <- mapM build t
                              tell $ IntMap.singleton n res
                              return n

-- | This function unravels a given graph to the term it
-- represents. The following property holds for 'termTree' and
-- 'unravelGraph':
-- 
-- @
-- unravelGraph (termTree x) == x
-- @
unravelGraph :: forall f. Functor f => Graph f -> Term f
unravelGraph g = build (_root g)
    where build :: Node -> Term f
          build n = Term $ fmap build $ lookupNode n (_eqs g)



graphCata :: forall f c . Functor f => Alg f c -> Graph f -> c
graphCata alg g = run (_root g)
    where run :: Node -> c
          run n = alg $ fmap run $ lookupNode n (_eqs g)

-- | Internal function used to lookup the nodes in a graph. It assumes
-- a node of a graph that is either the root node or a target node of
-- one of the edges. The implementation of this function makes use of
-- the invariant that each such node must also be in the domain of the
-- IntMap of the graph.
lookupNode :: Node -> IntMap (f Node) -> f Node
lookupNode n imap = fromJustNote "edge leading to an undefined node" $ IntMap.lookup n imap


-- | This function takes a term, and returns a 'Graph' with the
-- implicit sharing of the input data structure made explicit.
reifyGraph :: Traversable f => Term f -> IO (Graph f)
reifyGraph m = do (root, state) <- runStateT (findNodes m) init
                  return (Graph root (rsEqs state) (rsNext state))
    where  init = ReifyState
                  { rsStable = HashMap.empty
                  , rsEqs = IntMap.empty
                  , rsNext = 0 }

data ReifyState f = ReifyState
    { rsStable :: HashMap (StableName (f (Term f))) Node
    , rsEqs :: IntMap (f Node)
    , rsNext :: Node
    }

findNodes :: Traversable f => Term f -> StateT (ReifyState f) IO Node
findNodes (Term !j) = do
        st <- liftIO $ makeStableName j
        tab <- liftM rsStable get
        case HashMap.lookup st tab of
          Just var -> return $ var
          Nothing -> do var <- liftM rsNext get
                        modify (\s -> s{ rsNext = var + 1
                                       , rsStable = HashMap.insert st var tab})
                        res <- mapM findNodes j
                        modify (\s -> s { rsEqs = IntMap.insert var res (rsEqs s)})
                        return var
