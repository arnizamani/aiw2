module Merge where

mergeS :: (Eq a, Eq b) => [[(a,b)]] -> [[(a,b)]] -> [[(a,b)]]
mergeS [] _ = []
mergeS _ [] = []
mergeS xs ys = filter (not . null) $
                [[(x,a) | (x,a) <- x',(y,b) <- y',x == y, a == b]
                 ++ [(x,a) | (x,a) <- x', (lookup x y') == Nothing]
                 ++ [(y,b) | (y,b) <- y', (lookup y x') == Nothing]
                    | x' <- xs,y' <- ys]


x1 = [[("x","Circles")],[("x","Pircles")]]
y1 = [[("y","sun")]]
--      solution: [[("x",(Circles)),("y",(sun))],[("x",(Circles)),("y",(sun))]]

x2 = [[("x","Circles")],[("x","Circles")]]
y2 = [[("x","Circles"),("y","sun")]]
--      solution: [[("x",(Circles)),("y",(sun))],[("x",(Circles)),("y",(sun))]]

x3 = [[("x",1),("y",1)],[("x",0),("y",2)],[("x",2),("y",0)]]
y3 = [[("x",1),("y",1)]]
--      solution: [[("x",(1)),("y",(1))]]
