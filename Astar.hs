module AStar (aStar) where

import qualified Data.Set as Set
import Data.Set (Set, (\\))
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.PSQueue as PSQ
import Data.PSQueue (PSQ, Binding(..), minView)
import Data.List (foldl')

data AStar a c = AStar { visited  :: !(Set a),
                         waiting  :: !(PSQ a c),
                         score    :: !(Map a c),
                         memoHeur :: !(Map a c),
                         cameFrom :: !(Map a a),
                         end      :: !(Maybe a) }
    deriving Show
    
aStarInit start = AStar { visited  = Set.empty,
                          waiting  = PSQ.singleton start 0,
                          score    = Map.singleton start 0,
                          memoHeur = Map.empty,
                          cameFrom = Map.empty,
                          end      = Nothing }

runAStar :: (Ord a, Ord c, Num c) =>
         (a -> Set a)     -- adjacencies in graph
         -> (a -> a -> c) -- distance function
         -> (a -> c)      -- heuristic distance to goal
         -> (a -> Bool)   -- goal
         -> a             -- starting vertex
         -> AStar a c     -- final state

runAStar graph dist heur goal start = aStar' (aStarInit start)
  where aStar' s
          = case minView (waiting s) of
              Nothing            -> s
              Just (x :-> _, w') ->
                let graph' = graph x
                in if goal x && Set.null graph'
                    then s { end = Just x }
                    else aStar' $ foldl' (expand x)
                                         (s { waiting = w',
                                              visited = Set.insert x (visited s)})
                                         (Set.toList (graph' \\ visited s))
        expand x s y
          = let v = score s ! x + dist x y
            in case PSQ.lookup y (waiting s) of
                 Nothing -> link x y v
                              (s { memoHeur
                                     = Map.insert y (heur y) (memoHeur s) })
                 Just _  -> if v < score s ! y
                              then link x y v s
                              else s
        link x y v s
           = s { cameFrom = Map.insert y x (cameFrom s),
                 score    = Map.insert y v (score s),
                 waiting  = PSQ.insert y (v + memoHeur s ! y) (waiting s) }

-- | This function computes an optimal (minimal distance) path through a graph in a best-first fashion,
-- starting from a given starting point.
aStar :: (Ord a, Ord c, Num c) =>
         (a -> Set a)     -- ^ The graph we are searching through, given as a function from vertices
                          -- to their neighbours.
         -> (a -> a -> c) -- ^ Distance function between neighbouring vertices of the graph. This will
                          -- never be applied to vertices that are not neighbours, so may be undefined
                          -- on pairs that are not neighbours in the graph.
         -> (a -> c)      -- ^ Heuristic distance to the (nearest) goal. This should never overestimate the
                          -- distance, or else the path found may not be minimal.
         -> (a -> Bool)   -- ^ The goal, specified as a boolean predicate on vertices.
         -> a             -- ^ The vertex to start searching from.
         -> Maybe [a]     -- ^ An optimal path, if any path exists. This excludes the starting vertex.
aStar graph dist heur goal start
    = case end results of
        Nothing -> Nothing
        Just e  -> Just (reverse
                         . takeWhile (not . (== start))
                         . iterate (cameFrom results !)
                         $ e)
  where
    results = runAStar graph dist heur goal start

plane :: (Integer, Integer) -> Set (Integer, Integer)
plane (x,y) = Set.fromList [(x-1,y),(x+1,y),(x,y-1),(x,y+1)]

planeHole :: (Integer, Integer) -> Set (Integer, Integer)
planeHole (x,y) = Set.filter (\(u,v) -> planeDist (u,v) (0,0) > 10) (plane (x,y))

planeDist :: (Integer, Integer) -> (Integer, Integer) -> Double
planeDist (x1,y1) (x2,y2) = sqrt ((x1'-x2')^2 + (y1'-y2')^2)
    where [x1',y1',x2',y2'] = map fromInteger [x1,y1,x2,y2]


