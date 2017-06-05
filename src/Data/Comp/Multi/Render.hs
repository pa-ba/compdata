{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
module Data.Comp.Multi.Render where

import Data.Comp.Multi
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.Show()
import Data.Tree (Tree (..))
import Data.Tree.View

-- | The 'stringTree' algebra of a functor. The default instance creates a tree
-- with the same structure as the term.
class (HFunctor f, HFoldable f,ShowHF f,ShowConstr f) => Render f where
    stringTreeAlg :: Alg f (K (Tree String))
    stringTreeAlg f = K $ Node (showConstr f) $ fmap (\(E (K a)) -> a) $ htoList f

-- | Convert a term to a 'Tree'
stringTree :: Render f => Term f :-> K (Tree String)
stringTree = cata stringTreeAlg

-- | Show a term using ASCII art
showTerm :: Render f => Term f :=> String
showTerm = showTree . unK . stringTree

-- | Print a term using ASCII art
drawTerm :: Render f => Term f :=> IO ()
drawTerm = putStrLn . showTerm

-- | Write a term to an HTML file with foldable nodes
writeHtmlTerm :: Render f => FilePath -> Term f :=> IO ()
writeHtmlTerm file = writeHtmlTree file . fmap (\n -> NodeInfo n "") . unK . stringTree

$(derive [liftSum] [''Render])
