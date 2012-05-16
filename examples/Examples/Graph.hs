module Examples.Graph where

import Data.Comp.Graph
import Data.Comp.Graph.GraphViz
import Data.Comp
import Data.Comp.Show
import Data.Traversable

import Examples.Common

ex :: Term Sig
ex = (\x -> x `iAdd` x) (iConst 2 `iMult` iConst 1)


printGraph :: (Traversable f, ShowF f) => Term f -> IO ()
printGraph g = reifyGraph g >>= previewGraph