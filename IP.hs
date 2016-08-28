--    Environment for OccamStar 4
--    By Abdul Rahim Nizamani


Notes:
--Rewarded symbols: 0,1,2,... and #, but not + and * (those that appear in rhs of items).
--A goal is defined as an Exp that only contains rewarding symbols.

--Confluence checking.
--sigma(t) -> x
--sigma(t') -> y, then x == y, and x and y are goal expressions.

--Update last seen time for axioms

--update structure of shape, use maps or sets

--Use axiom recency when removing axioms (when viabilities are same)



Suggestion:
if
2 . 0 = 0
3 . 0 = 0
then, x . 0 = 0, and above two go to evidence store.
if x . 0 = 0 turns out to be wrong, remove it and add the evidence to ltm.

Each variable should have at least two examples.
So x+y=y+x should have 2*2 = 4 examples at least.

Some visualization of the program run: Such as recent changes in theory, most used axioms, etc.

Automatize the learning: generate stream of examples (bigger examples with decreasing frequency, and neg examples).

Store substitutions in shapes instead of answers

x#y = x+y

Check consistency of all axioms at each instance. Use only small substitutions.

Current program name: Popper

Later program name: Collector : adds a new 

Leibeg near Kiel, an old town


0#1 = 1
0+1 = 1

0#2 = 2

0#y = 0+y

((Alice # runs) # to)
Alice walks

Bob runs
Bob walks

Alice -> Bob


--((f 1),(8),1)
--((f 2),(1 # 1),1)
--((f 3),(1 # 4),1)
--((f (1 # 0)),(3 # 5),1)


--((0 # 1),1,1)
((0 # 2),(2),1)

--((0 + 0),0,1)
--((0 + 1),1,1)
--((0 + 2),2,1)
--((0 + 3),3,1)
--((0 + 4),4,1)
--((0 + 5),5,1)
--((0 + 6),6,1)
--((0 + 7),7,1)
--((0 + 8),8,1)
--((0 + 9),9,1)
--((0 + (1 # 0)),(1 # 0),1)
--((0 + (1 # 1)),(1 # 1),1)

--((1 + 0),1,1)
--((1 + 1),2,1)
--((1 + 2),3,1)
--((1 + 3),4,1)
--((1 + 4),5,1)
--((1 + 5),6,1)
--((1 + 6),7,1)
--((1 + 7),8,1)
--((1 + 8),9,1)
--((1 + 9),(1 # 0),1)

--((2 + 0),2,1)
--((2 + 1),3,1)
--((2 + 2),4,1)
--((2 + 3),5,1)
--((2 + 4),6,1)
--((2 + 5),7,1)
--((2 + 6),8,1)
--((2 + 7),9,1)
--((2 + 8),(1 # 0),1)
--((2 + 9),(1 # 1),1)

--((3 + 0),3,1)
--((3 + 1),4,1)
--((3 + 2),5,1)
--((3 + 3),6,1)
--((3 + 4),7,1)
--((3 + 5),8,1)
--((3 + 6),9,1)
--((3 + 7),(1 # 0),1)
--((3 + 8),(1 # 1),1)
--((3 + 9),(1 # 2),1)

--((4 + 0),4,1)
--((4 + 1),5,1)
--((4 + 2),6,1)
--((4 + 3),7,1)
--((4 + 4),8,1)
--((4 + 5),9,1)
--((4 + 6),(1 # 0),1)
--((4 + 7),(1 # 1),1)
--((4 + 8),(1 # 2),1)
--((4 + 9),(1 # 3),1)

--((5 + 0),5,1)
--((5 + 1),6,1)
--((5 + 2),7,1)
--((5 + 3),8,1)
--((5 + 4),9,1)
--((5 + 5),(1 # 0),1)
--((5 + 6),(1 # 1),1)
--((5 + 7),(1 # 2),1)
--((5 + 8),(1 # 3),1)
--((5 + 9),(1 # 4),1)

--((6 + 0),6,1)
--((6 + 1),7,1)
--((6 + 2),8,1)
--((6 + 3),9,1)
--((6 + 4),(1 # 0),1)
--((6 + 5),(1 # 1),1)
--((6 + 6),(1 # 2),1)
--((6 + 7),(1 # 3),1)
--((6 + 8),(1 # 4),1)
--((6 + 9),(1 # 5),1)

--((7 + 0),7,1)
--((7 + 1),8,1)
--((7 + 2),9,1)
--((7 + 3),(1 # 0),1)
--((7 + 4),(1 # 1),1)
--((7 + 5),(1 # 2),1)
--((7 + 6),(1 # 3),1)
--((7 + 7),(1 # 4),1)
--((7 + 8),(1 # 5),1)
--((7 + 9),(1 # 6),1)

--((8 + 0),8,1)
--((8 + 1),9,1)
--((8 + 2),(1 # 0),1)
--((8 + 3),(1 # 1),1)
--((8 + 4),(1 # 2),1)
--((8 + 5),(1 # 3),1)
--((8 + 6),(1 # 4),1)
--((8 + 7),(1 # 5),1)
--((8 + 8),(1 # 6),1)
--((8 + 9),(1 # 7),1)

--((9 + 0),9,1)
--((9 + 1),(1 # 0),1)
--((9 + 2),(1 # 1),1)
--((9 + 3),(1 # 2),1)
--((9 + 4),(1 # 3),1)
--((9 + 5),(1 # 4),1)
--((9 + 6),(1 # 5),1)
--((9 + 7),(1 # 6),1)
--((9 + 8),(1 # 7),1)
--((9 + 9),(1 # 8),1)

--(((1 # 0) + 0),(1 # 0),1)
--(((1 # 0) + 1),(1 # 1),1)
--(((1 # 0) + 2),(1 # 2),1)
--(((1 # 0) + 3),(1 # 3),1)
--(((1 # 0) + 4),(1 # 4),1)
--(((1 # 0) + 5),(1 # 5),1)
--(((1 # 0) + 6),(1 # 6),1)
--(((1 # 0) + 7),(1 # 7),1)
--(((1 # 0) + 8),(1 # 8),1)
--(((1 # 0) + 9),(1 # 9),1)




--((0 * 1),0,1)
--((0 * 2),0,1)

--((1 * 0),0,1)
--((1 * 1),1,1)

--((2 + 3),5,1)
--((3 + 2),5,1)

--((4 + 3),7,1)
--((3 + 4),7,1)

--((9 + 5),(1 # 4),1)
--((5 + 9),(1 # 4),1)

--((2 * 0),0,1)
--((2 * 1),2,1)
--((2 * 2),4,1)
--((2 * 3),6,1)
--((2 * 4),8,1)
--((2 * 5),(1 # 0),1)
--((2 * 6),(1 # 2),1)
--((2 * 7),(1 # 4),1)
--((2 * 8),(1 # 6),1)
--((2 * 9),(1 # 8),1)

--((3 * 2),6,1)
--((3 * 3),9,1)
--((3 * 4),(1 # 2),1)
--((3 * 5),(1 # 5),1)
--((3 * 6),(1 # 8),1)
--((3 * 7),(2 # 1),1)
--((3 * 8),(2 # 4),1)
--((3 * 9),(2 # 7),1)

--((4 * 2),8,1)
--((4 * 3),(1 # 2),1)
--((4 * 4),(1 # 6),1)
--((4 * 5),(2 # 0),1)
--((4 * 6),(2 # 4),1)
--((4 * 7),(2 # 8),1)
--((4 * 8),(3 # 2),1)
--((4 * 9),(3 # 6),1)

--((5 * 2),(1 # 0),1)
--((5 * 3),(1 # 5),1)
--((5 * 4),(2 # 0),1)
--((5 * 5),(2 # 5),1)
--((5 * 6),(3 # 0),1)
--((5 * 7),(3 # 5),1)
--((5 * 8),(4 # 0),1)
--((5 * 9),(4 # 5),1)

--((6 * 2),(1 # 2),1)
--((6 * 3),(1 # 8),1)
--((6 * 4),(2 # 4),1)
--((6 * 5),(3 # 0),1)
--((6 * 6),(3 # 6),1)
--((6 * 7),(4 # 2),1)
--((6 * 8),(4 # 8),1)
--((6 * 9),(5 # 4),1)

--((7 * 2),(1 # 4),1)
--((7 * 3),(2 # 1),1)
--((7 * 4),(2 # 8),1)
--((7 * 5),(3 # 5),1)
--((7 * 6),(4 # 2),1)
--((7 * 7),(4 # 9),1)
--((7 * 8),(5 # 6),1)
--((7 * 9),(6 # 3),1)

--((8 * 2),(1 # 6),1)
--((8 * 3),(2 # 4),1)
--((8 * 4),(3 # 2),1)
--((8 * 5),(4 # 0),1)
--((8 * 6),(4 # 8),1)
--((8 * 7),(5 # 6),1)
--((8 * 8),(6 # 4),1)
--((8 * 9),(7 # 2),1)

--((9 * 2),(1 # 8),1)
--((9 * 3),(2 # 7),1)
--((9 * 4),(3 # 6),1)
--((9 * 5),(4 # 5),1)
--((9 * 6),(5 # 4),1)
--((9 * 7),(6 # 3),1)
--((9 * 8),(7 # 2),1)
--((9 * 9),(8 # 1),1)

--((0 _ 0),0,1)
--((0 _ 1),(- 1),1)
--((0 _ 2),(- 2),1)
--((0 _ 3),(- 3),1)
--((0 _ 4),(- 4),1)
--((0 _ 5),(- 5),1)
--((0 _ 6),(- 6),1)
--((0 _ 7),(- 7),1)
--((0 _ 8),(- 8),1)
--((0 _ 9),(- 9),1)

--((1 _ 0),1,1)
--((1 _ 1),0,1)
--((1 _ 2),(- 1),1)
--((1 _ 3),(- 2),1)
--((1 _ 4),(- 3),1)
--((1 _ 5),(- 4),1)
--((1 _ 6),(- 5),1)
--((1 _ 7),(- 6),1)
--((1 _ 8),(- 7),1)
--((1 _ 9),(- 8),1)

--((2 _ 1),1,1)
--((2 _ 3),(- 1),1)
--((2 _ 4),(- 2),1)
--((2 _ 5),(- 3),1)
--((2 _ 6),(- 4),1)
--((2 _ 7),(- 5),1)
--((2 _ 8),(- 6),1)
--((2 _ 9),(- 7),1)

--((3 _ 1),2,1)
--((3 _ 2),1,1)
--((3 _ 4),(- 1),1)
--((3 _ 5),(- 2),1)
--((3 _ 6),(- 3),1)
--((3 _ 7),(- 4),1)
--((3 _ 8),(- 5),1)
--((3 _ 9),(- 6),1)

--((4 _ 1),3,1)
--((4 _ 2),2,1)
--((4 _ 3),1,1)
--((4 _ 5),(- 1),1)
--((4 _ 6),(- 2),1)
--((4 _ 7),(- 3),1)
--((4 _ 8),(- 4),1)
--((4 _ 9),(- 5),1)

--((5 _ 1),4,1)
--((5 _ 2),3,1)
--((5 _ 3),2,1)
--((5 _ 4),1,1)
--((5 _ 6),(- 1),1)
--((5 _ 7),(- 2),1)
--((5 _ 8),(- 3),1)
--((5 _ 9),(- 4),1)

--((6 _ 1),5,1)
--((6 _ 2),4,1)
--((6 _ 3),3,1)
--((6 _ 4),2,1)
--((6 _ 5),1,1)
--((6 _ 7),(- 1),1)
--((6 _ 8),(- 2),1)
--((6 _ 9),(- 3),1)

--((7 _ 1),6,1)
--((7 _ 2),5,1)
--((7 _ 3),4,1)
--((7 _ 4),3,1)
--((7 _ 5),2,1)
--((7 _ 6),1,1)
--((7 _ 8),(- 1),1)
--((7 _ 9),(- 2),1)

--((8 _ 1),7,1)
--((8 _ 2),6,1)
--((8 _ 3),5,1)
--((8 _ 4),4,1)
--((8 _ 5),3,1)
--((8 _ 6),2,1)
--((8 _ 7),1,1)
--((8 _ 9),(- 1),1)

--((9 _ 1),8,1)
--((9 _ 2),7,1)
--((9 _ 3),6,1)
--((9 _ 4),5,1)
--((9 _ 5),4,1)
--((9 _ 6),3,1)
--((9 _ 7),2,1)
--((9 _ 8),1,1)

--((1 / 1),1,1)
--((2 / 1),2,1)

--((0 / 2),0,1)
--((2 / 2),1,1)
--((4 / 2),2,1)
--((6 / 2),3,1)
--((8 / 2),4,1)
--(((1 # 0) / 2),5,1)
--(((1 # 2) / 2),6,1)
--(((1 # 4) / 2),7,1)
--(((1 # 6) / 2),8,1)
--(((1 # 8) / 2),9,1)

--((0 / 3),0,1)
--((6 / 3),2,1)
--((9 / 3),3,1)
--(((1 # 2) / 3),4,1)
--(((1 # 5) / 3),5,1)
--(((1 # 8) / 3),6,1)
--(((2 # 1) / 3),7,1)
--(((2 # 4) / 3),8,1)
--(((2 # 7) / 3),9,1)

--((8 / 4),2,1)
--(((1 # 2) / 4),3,1)
--(((1 # 6) / 4),4,1)
--(((2 # 0) / 4),5,1)
--(((2 # 4) / 4),6,1)
--(((2 # 8) / 4),7,1)
--(((3 # 2) / 4),8,1)
--(((3 # 6) / 4),9,1)

--(((1 # 0) / 5),2,1)
--(((1 # 5) / 5),3,1)
--(((2 # 0) / 5),4,1)
--(((2 # 5) / 5),5,1)
--(((3 # 0) / 5),6,1)
--(((3 # 5) / 5),7,1)
--(((4 # 0) / 5),8,1)
--(((4 # 5) / 5),9,1)

--(((1 # 2) / 6),2,1)
--(((1 # 8) / 6),3,1)
--(((2 # 4) / 6),4,1)
--(((3 # 0) / 6),5,1)
--(((3 # 6) / 6),6,1)
--(((4 # 2) / 6),7,1)
--(((4 # 8) / 6),8,1)
--(((5 # 4) / 6),9,1)

--(((1 # 4) / 7),2,1)
--(((2 # 1) / 7),3,1)
--(((2 # 8) / 7),4,1)
--(((3 # 5) / 7),5,1)
--(((4 # 2) / 7),6,1)
--(((4 # 9) / 7),7,1)
--(((5 # 6) / 7),8,1)
--(((6 # 3) / 7),9,1)

--(((1 # 6) / 8),2,1)
--(((2 # 4) / 8),3,1)
--(((3 # 2) / 8),4,1)
--(((4 # 0) / 8),5,1)
--(((4 # 8) / 8),6,1)
--(((5 # 6) / 8),7,1)
--(((6 # 4) / 8),8,1)
--(((7 # 2) / 8),9,1)

--(((1 # 8) / 9),2,1)
--(((2 # 7) / 9),3,1)
--(((3 # 6) / 9),4,1)
--(((4 # 5) / 9),5,1)
--(((5 # 4) / 9),6,1)
--(((6 # 3) / 9),7,1)
--(((7 # 2) / 9),8,1)
--(((8 # 1) / 9),9,1)

-- x#0 + y = x#y
--(((1 # 0) + 2),(1 # 2),1)
--(((2 # 0) + 5),(2 # 5),1)
--(((3 # 0) + 5),(3 # 5),1)

-- x + y#0 = y#x
--((2 + (1 # 0)),(1 # 2),1)
--((3 + (1 # 0)),(1 # 3),1)

--((- 0),0,1)

--   --x = x
--((- (- 1)),1,1)
--((- (- 2)),2,1)

--  (x#y) + z = x#(y + z)
--(((6 # 5) + 3),(6 # 8),1)
--((6 # (5 + 3)),(6 # 8),1)
--(((2 # 3) + 4),(2 # 7),1)
--((2 # (3 + 4)),(2 # 7),1)
--(((2 # 5) + 4),(2 # 9),1)
--((2 # (5 + 4)),(2 # 9),1)
--(((6 # 2) + 3),(6 # 5),1)
--((6 # (2 + 3)),(6 # 5),1)
--(((5 # 2) + 3),(5 # 5),1)
--((5 # (2 + 3)),(5 # 5),1)

--  x + (y#z) = y#(x + z)
-- ((5 + (7 # 4)),(7 # 9),1)

--  x#(y#z) ==> (x+y)#z
--((6 # (1 # 7)),(7 # 7),1)
--((6 # (2 # 7)),(8 # 7),1)
--(((6 + 1) # 7),(7 # 7),1)
--(((6 + 2) # 7),(8 # 7),1)
--((3 # (1 # 7)),(4 # 7),1)
--((4 # (1 # 7)),(5 # 7),1)

-- Commutativity of addition: x + y = y + x
--(((2 # 1) + 3),(2 # 4),1)
--((3 + (2 # 1)),(2 # 4),1)



-- LEARNED WRONG:

-- xy * z  = (x*z)y
--(((2 # 0) * 3),(6 # 0),1)

-- x * yz  = (x*y)z
--((3 * (2 # 0)),(6 # 0),1)

-- NOT LEARNED

--  x#(y#z) ==> (y+x)#z



--  x*(y#z) ==> (x*y)#(x*z)


--  (x#y)*z ==> (x*z)#(y*z)
--(((1 # 3) * 2),(2 # 6),1)
--(((1 * 2) # (3 * 2)),(2 # 6),1)

--(((2 # 3) * 3),(6 # 9),1)
--(((2 * 3) # (3 * 3)),(6 # 9),1)

--(((1 # 3) * 3),(3 # 9),1)
--(((1 * 3) # (3 * 3)),(3 # 9),1)

--(((1 # 3) * 4),(5 # 2),1)
--(((1 * 4) # (3 * 4)),(5 # 2),1)

-- Associativity of addition: x + (y + z) = (x + y) + z
--((2 + (3 + 4)),((2 + 3) + 4),1)

-- Associativity of addition: (x + y) + z = x + (y + z)
--(((2 + 3) + 4),(2 + (3 + 4)),1)


-- (x#y) = (x#0) + y
--((1 # 2),((1 # 0) + 2),1)
--((1 # 2),((1 # 3) + 2),-1)


-- (x+y)*z = x*z + y*z
--(((1 + 2) * 3),((1 * 3) + (2 * 3)),1)

-- (x#y) * z = x*z + y*z
--(((1 # 2) * 8),((1 * 8) + (2 * 8)),1)


-- test: addition
--(((3 # 4) + 8),(4 # 2),1)
--(((3 # 4) + (1 # 2)),(4 # 6),1)
--(((7 # 4) + (2 # 2)),(9 # 6),1)
--(((7 # 4) + (3 # 2)),((1 # 0) # 6),1)
--(((9 # 9) + (7 # 8)),((1 # 7) # 7),1)
--((((2 # 3) # 4) + 3),((2 # 3) # 7),1)

-- fails:
--((((2 # 3) # 4) + (3 + 2)),((2 # 6) # 6),1)

-- test: passed
--(((6 # 7) * 8),((5 # 3) # 6),1)

-- test: failed
--(((7 # 9) * (1 # 0)),((7 # 9) # 0),1)


--(((6 * 8) # (7 * 8)),((5 # 3) # 6),1)
--(((6 # 7) * 8),((6 * 8) # (7 * 8)),1)
--(,((5 # 3) # 6),1)
--(((6 # 7) * 8),(((6 * 8) # 0) + (7 * 8)),1)
--((((6 * 8) # 0) + (7 * 8)),(((4 # 8) + 5) # 6),1)
--((((4 # 8) + 5) # 6),((5 # 3) # 6),1)



-- computation:
-- 6#7 * 8          -- 5
-- (6#0 + 7) * 8    -- 7
-- 6#0 * 8 + 7 * 8  -- 9
-- (6*8)#0 + 7 * 8  -- 9
-- (4#8)#0 + 7 * 8  -- 9
-- (4#8)#0 + 5#6    -- 9
-- (4#8)#(5#6)      -- 7
-- ((4#8) + 5)#6    -- 7
-- (4#(8+5))#6      -- 7
-- (4#(1#3))#6      -- 7
-- ((4+1)#3)#6      -- 7
-- (5#3)#6          -- 5


---------------------------------------------------
--            LANGUAGE GRAMMAR                   --
---------------------------------------------------

-- ((Alice _ crawls),OK,1)





---------------------------------------------------
---------------------------------------------------

Example 12(b): done

8+3 = 1#1
1#1 + 3 = 1#4

f(1) = f(0+1)
f(2) = f(1+1)
f(3) = f(2+1)

f(1)
f(0+1)
f(0)+3
8+3
1#1

f(2)
f(1+1)
f(1)+3
f(0+1) + 3
(f(0) + 3) + 3
(8 + 3) + 3
1:1 + 3
1:4

(6:7)*8
(6*8):(7*8) -- (x:y)*z ->> (x*z):(y*z)
(6*8):(5:6) -- 7*8 ->> 5:6
(4:8):(5:6) -- 6*8 ->> 4:8
((4:8)+5):6 -- x:(y:z) ->> (x+y):z
(4:(8+5)):6 -- (x:y)+z ->> x:(y+z)
(4:(1:3)):6 -- 8+5 ->> 1:3
((4+1):3):6 -- x:(y:z) ->> (x+y):z
(5:3):6     -- 4+1 ->> 5

f(3)
f(2+1)      -- f(3) ->> f(2+1)
f(2)+3      -- 
f(1+1)+3    -- 
(f(1)+3)+3  -- 
(f(0+1)+3)+3  
((f(0)+3)+3)+3  
((8+3)+3)+3
(1:1 + 3) +3
(1:4) + 3
1:7


-------------------------------------------------------------------------------
--                     PROPOSITIONAL LOGIC                                   --
-------------------------------------------------------------------------------

----------------------- LHS is length 7
-- A55
--((| (& P Q) (& P R)),(& P (| Q R)),1)
-- A56
--((& (| P Q) (| P R)),(| P (& Q R)),1)

----------------------- LHS is length 6
-- A68
--((not (& (not P) (not Q))),(| P Q),1)
-- A76
--((not (| (not P) (not Q))),(& P Q),1)

----------------------- LHS is length 5
-- A21
--((-> (& P Q) P),T,1)
--((-> Q P),T,-1)
-- A22
--((-> (& Q R) R),T,1)
--((-> (& P Q) Q),T,1)
--((-> (& Q R) R),T,1)
--((-> (& P F) F),T,1)
--((-> Q P),T,-1)
-- A23             x -> (x | y) ->> T
--((-> P (| P Q)),T,1)
--((-> P Q),T,-1)
-- A24             x -> (y | x) ->> T
--((-> Q (| P Q)),T,1)
--((-> R (| P R)),T,1)
--((-> (not P) (| Q (not P))),T,1)
--((-> P Q),T,-1)
-- A47
--((& (& P Q) R),(& P (& Q R)),1)
-- A48
--((& P (& Q R)),(& (& P Q) R),1)
-- A49
--((| (| P Q) R),(| P (| Q R)),1)
-- A50
--((| P (| Q R)),(| (| P Q) R),1)
-- A51
--((<-> (<-> P Q) R),(<-> P (<-> Q R)),1)
-- A52
--((<-> P (<-> Q R)),(<-> (<-> P Q) R),1)
-- A53
--((& P (| Q R)),(| (& P Q) (& P R)),1)
-- A54
--((| P (& Q R)),(& (| P Q) (| P R)),1)
-- A64
--((-> (not Q) (not P)),(-> P Q),1)
--((-> (not P) (not R)),(-> R P),1)
--((-> (not Q) (not R)),(-> R Q),1)
-- A66
--((& (not P) (not Q)),(not (| P Q)),1)
-- A70
--((not (& P (not Q))),(| (not P) Q),1)
--((not (& Q (not R))),(| (not Q) R),1)
--((not R),(| (not P) Q),-1)
-- A72
--((not (& (not P) Q)),(| P (not Q)),1)
--((not (& (not Q) R)),(| Q (not R)),1)
-- A74
--((| (not P) (not Q)),(not (& P Q)),1)
-- A78
--((not (| P (not Q))),(& (not P) Q),1)
--((not (| Q (not R))),(& (not Q) R),1)
-- A80
--((not (| (not P) Q)),(& P (not Q)),1)
--((not (| (not Q) R)),(& Q (not R)),1)

----------------------- LHS is length 4
-- A19
--((| P (not P)),T,1)
--((| Q (not Q)),T,1)
--((| P Q),T,-1)
-- A20
--((| (not P) P),T,1)
--((| (not Q) Q),T,1)
--((| P Q),T,-1)
-- A28
--((& P (not P)),F,1)
--((& Q (not Q)),F,1)
--((& Q P),F,-1)
-- A29
--((& (not P) P),F,1)
--((& (not Q) Q),F,1)
--((& Q P),F,-1)
-- A30
--((<-> P (not P)),F,1)
--((<-> Q (not Q)),F,1)
--((not P),F,-1)
--((<-> Q P),F,-1)
-- A31
--((<-> (not P) P),F,1)
--((<-> (not Q) Q),F,1)
--((<-> Q P),F,-1)
-- A58
--((-> P (not P)),(not P),1)
--((-> Q (not Q)),(not Q),1)
--((-> R (not R)),(not R),1)
--((-> Q Q),(not Q),-1)
--((-> Q Q),Q,-1)
-- A59
--((-> (not P) P),P,1)
--((-> (not Q) Q),Q,1)
--((-> (not R) R),R,1)
--((-> Q Q),Q,-1)
-- A60
--((| (not P) Q),(-> P Q),1)
-- A62
--((not (-> P Q)),(& P (not Q)),1)
-- A63
--((& P (not Q)),(not (-> P Q)),1)
-- A67
--((not (| P Q)),(& (not P) (not Q)),1)
-- A71
--((| (not P) Q),(not (& P (not Q))),1)
-- A73
--((| P (not Q)),(not (& (not P) Q)),1)
-- A75
--((not (& P Q)),(| (not P) (not Q)),1)
-- A79
--((& (not P) Q),(not (| P (not Q))),1)
-- A81
--((& P (not Q)),(not (| (not P) Q)),1)

--------------------------- Shallow axioms
-- A85             x -> y ---> not x
--      not learned
--((-> P Q),(not P),1)
--((-> Q P),(not Q),1)
--((-> Q P),Q,-1)
--((& R (-> P Q)),(& R (not P)),-1)

----------------------- LHS is length 3
-- A13
--((| P T),T,1)
--((| Q T),T,1)
--((| Q F),F,-1)
-- A32
--((| P F),P,1)
--((| Q F),Q,1)
--((| R F),R,1)
--((| P T),P,-1)
-- A33
--((| F P),P,1)
--((| F Q),Q,1)
--((| F R),R,1)
--((| T Q),Q,-1)
-- A14
--((| T P),T,1)
--((| F P),F,-1)
-- A15
--((-> P T),T,1)
--((-> Q T),T,1)
--((-> Q F),F,-1)
-- A16
--((-> F P),T,1)
--((-> F (& P Q)),T,1)
--((-> T P),T,-1)
-- A17
--((-> P P),T,1)
--((-> (not Q) (not Q)),T,1)
--((-> R R),T,1)
--((-> P Q),T,-1)
-- A18
--((<-> P P),T,1)
--((<-> Q Q),T,1)
--((<-> P Q),T,-1)
-- A26
--((& P F),F,1)
--((& Q F),F,1)
--((& Q T),T,-1)
-- A27
--((& F P),F,1)
--((& F Q),F,1)
--((& F R),F,1)
--((& T Q),T,-1)
-- A34
--((& P T),P,1)
--((& Q T),Q,1)
--((& R T),R,1)
--((& Q F),Q,-1)
-- A35
--((& T P),P,1)
--((& T Q),Q,1)
--((& T R),R,1)
--((& F Q),Q,-1)
-- A36
--((-> T P),P,1)
--((-> T Q),Q,1)
--((-> T R),R,1)
--((-> F Q),Q,-1)
-- A84             x -> y ---> y
--(P :-> Q,Q,1)
--(Q :-> P,P,1)
--(Q :-> R,R,1)
--(R :& (Q :-> P),R :& P,-1)
-- A37
--(P :-> F,not P,1)
--(Q :-> F,not Q,1)
--(R :-> F,not R,1)
--(Q :-> T,not Q,-1)
-- A38
--(P :<-> T,P,1)
--(Q :<-> T,Q,1)
--(R :<-> T,R,1)
--(Q :<-> F,Q,-1)
-- A39
--(T :<-> P,P,1)
--(T :<-> Q,Q,1)
--(T :<-> R,R,1)
--(F :<-> Q,Q,-1)
-- A40
--(P :<-> F,not P,1)
--(Q :<-> F,not Q,1)
--(R :<-> F,not R,1)
--(Q :<-> T,not Q,-1)
-- A41
--(F :<-> P,not P,1)
--(F :<-> Q,not Q,1)
--(F :<-> R,not R,1)
--(T :<-> Q,not Q,-1)
-- A42
--(P :& P,P,1)
--(Q :& Q,Q,1)
-- A43
--(P :| P,P,1)
--(Q :| Q,Q,1)
-- A83             x | y ---> y
--(P :| Q,Q,1)
--(Q :| P,P,1)
--(Q :| R,R,1)
--(P :| R,R,1)
--((P :| Q) :& R,Q :& R,-1)
-- A82             x | y ---> x
--(Q :| R,Q,1)
--(Q :| P,Q,1)
--(R :| P,R,1)
--((not P) :| Q,not P,1)
--((P :| Q) :& R,P :& R,-1)
-- A57
--((not (not P)),P,1)
--((not P),P,-1)
-- A44
--(P :& Q,Q :& P,1)
--(P :& R,R :& P,1)
-- A45
--(P :| Q,Q :| P,1)
--(P :| R,R :| P,1)
-- A46
--(P :<-> Q,Q :<-> P,1)
--(P :<-> R,R :<-> P,1)
-- A65
--(R :-> P,(not P) :-> (not R),1)
-- A61
--(P :-> Q,(not P) :| Q,1)
-- A69
--(P :| Q,not ((not P) :& (not Q)),1)
-- A77
--(P :& Q,not ((not P) :| (not Q)),1)

----------------------- LHS is length 2
-- A12
--(not F,T,1)
--(not P,T,-1)
-- A25
--(not T,F,1)
--(T,F,-1)
--(not P,F,-1)



-------------------------------------------------------------------------------
--                                 TAUTOLOGIES                               --
-------------------------------------------------------------------------------

-- 1  solved with Taut, length = 4
-- Deep: 4
--((-> P (| (-> (not (not P)) P) Q)),T,1)
-- P :-> (((not (not P)) :-> P) :| Q)
-- ((not (not P)) :-> P) :| Q
-- (not (not P)) :-> P
-- P :-> P
-- T

-- 2  solved with Taut, length = 2
-- Deep: 2
--((-> (<-> (not P) P) (<-> Q Q)),T,1)
-- ((not P) :<-> P) :-> (Q :<-> Q)
-- Q :<-> Q
-- T

-- 3  solved with Taut, length = 3
-- Deep: 3
--((P :| P) :<-> (not (not P)),T,1)
-- (P :| P) :-> (not (not P))
-- P :-> (not (not P))
-- P :-> P
-- T

-- 5  solved with Taut, length = 2
-- Deep: 2
--(((not P) :& P) :-> Q,T,1)
-- ((not P) :& P) :-> Q
-- F :-> Q
-- T

-- 7  solved with Taut, length = 2
-- Deep: 2
--(P :-> (Q :-> P),T,1)
-- P :-> (Q :-> P)
-- P :-> ((not Q) :| P)
-- T

-- 9  solved with Taut, length = 2
-- Deep: 2
--(not ((not P) :<-> P),T,1)
-- not ((not P) :<-> P)
-- not F
-- T

-- 10  not solved
-- Deep: solved with WM=9, length=4
--((not (P :-> Q) :& R) :-> (not Q),T,1)
-- requires shallow axiom:  P :& Q -> R  -->  P -> R
-- solution with wm=9:
-- ((not (P :-> Q)) :& R) :-> (not Q)
-- ((P :& (not Q)) :& R) :-> (not Q)
-- (((not Q) :& P) :& R) :-> (not Q)
-- ((not Q) :& (P :& R)) :-> (not Q)
-- T

-- 11  solved with Taut, length = 3
-- Deep: 3
--(not (not (not (P :& (not P)))),T,1)
-- not (not (not (P :& (not P))))
-- not (P :& (not P))
-- not F
-- T

-- 12  solved with Taut, length = 2
-- Deep: 2
--((P :-> P) :| Q,T,1)
-- (P :-> P) :| Q
-- P :-> P
-- T

-- 15  solved with Taut, length = 2
-- Deep: 2
--((P :& P) :| (not P),T,1)
-- (P :& P) :| (not P)
-- P :| (not P)
-- T

-- 17  solved with Taut, length = 4
-- Deep: 4
--(P :| (P :| not (Q :& P)),T,1)
-- P :| (P :| (not (Q :& P)))
-- P :| ((not (Q :& P)) :| P)
-- P :| ((Q :& P) :-> P)
-- (Q :& P) :-> P
-- T

-- 18  solved with Taut, length = 2
-- Deep: 2
--((P :<-> (not P)) :-> (Q :<-> P),T,1)
-- (P :<-> (not P)) :-> (Q :<-> P)
-- F :-> (Q :<-> P)
-- T

-- 21  not solved
-- Deep: not solved
-- Shallow: solved with WM=10, length=5
--(not ((P :-> (not Q)) :| P) :-> Q,T,1)
-- (not ((P :-> (not Q)) :| P)) :-> Q
-- not (((not P) :| (not Q)) :| P)  :->  Q
-- not (((not Q) :| (not P)) :| P)  :->  Q
-- not ((not Q) :| ((not P) :| P))  :->  Q
-- Q :& (not ((not P) :| P))  :-> Q
-- T

-- 22  solved with Taut, length = 4
-- Deep: 4
--(((P :| (not Q)) :| Q) :| P,T,1)
-- ((P :| (not Q)) :| Q) :| P
-- (P :| (not Q)) :| Q
-- (not ((not P) :& Q)) :| Q
-- ((not P) :& Q) :-> Q
-- T

-- 28  solved with Taut, length = 1
-- Deep: 1
--((P :& P) :-> P,T,1)
-- (P :& P) :-> P
-- T

-- 29  solved with Taut, length = 2
-- Deep: 2
--((P :& P) :<-> P,T,1)
-- (P :& P) :<-> P
-- P :<-> P
-- T

-- 32  solved with Taut, length = 3
-- Deep: 3
--((not (not (P :-> Q))) :| (not Q),T,1)
-- (not (not (P :-> Q))) :| (not Q)
-- (not (P :-> Q)) :-> (not Q)
-- (P :& (not Q)) :-> (not Q)
-- T

-- 33  solved with Taut, length = 6
-- Deep:  6
--((P :<-> (Q :<-> (P :| P))) :-> Q,T,1)
-- (P :<-> (Q :<-> (P :| P))) :-> Q
-- (P :<-> (Q :<-> P)) :-> Q
-- ((Q :<-> P) :<-> P) :-> Q
-- (Q :<-> (P :<-> P)) :-> Q
-- (Q :<-> T) :-> Q
-- Q :-> Q
-- T

-- 35  solved with Taut, length = 2
-- Deep: 2
--((P :<-> P) :| (P :& (not Q)),T,1)
-- (P :<-> P) :| (P :& (not Q))
-- P :<-> P
-- T

-- 37  solved with Taut, length = 5
-- Deep: 5
--((P :& Q) :-> (Q :| R),T,1)
-- (P :& Q) :-> (Q :| R)
-- (not (P :& Q)) :| (Q :| R)
-- ((not (P :& Q)) :| Q) :| R
-- (not (P :& Q)) :| Q
-- (P :& Q) :-> Q
-- T

-- 40  solved with Taut, length = 1
-- Deep: 1
--((not P) :<-> (not P),T,1)
-- (not P) :<-> (not P)
-- T

-- 42  solved with Taut, length = 3
-- Deep: 3
--(((not P) :| Q) :| P,T,1)
-- ((not P) :| Q) :| P
-- (not P) :| (Q :| P)
-- P :-> (Q :| P)
-- T

-- 43  solved with Taut, length = 3
-- Deep: 3
--((not (P :-> P)) :-> Q,T,1)
-- (not (P :-> P)) :-> Q
-- not (not (P :-> P))
-- not (not T)
-- T

-- 44  solved with Taut, length = 2
-- Deep: 2
--(P :<-> (not (not P)),T,1)
-- P :<-> (not (not P))
-- P :<-> P
-- T

-- 45  not solved at wm=9
-- Deep: not solved
--(P :-> ((P :<-> Q) :| (Q :-> R)),T,1)
--    P :-> ((P :<-> Q) :| (Q :-> R))
--    (not P) :| ((P :<-> Q) :| (Q :-> R))
--    ((not P) :| (P :<-> Q)) :| (Q :-> R)
--    (P :-> Q) :| (Q :-> R)
--((P :-> Q) :| (Q :-> R),T,1): proved

-- 50  solved with Taut, length = 2
-- Deep: 2
--((P :-> Q) :-> (P :-> P),T,1)
-- (P :-> Q) :-> (P :-> P)
-- P :-> P
-- T

-- 52  solved with Taut, length = 2
-- Deep: 2
--((not (P :& P)) :| (Q :-> Q),T,1)
-- (not (P :& P)) :| (Q :-> Q)
-- Q :-> Q
-- T

-- 56  solved with Taut, length = 4
-- Deep: 4
--(P :| (P :-> (not Q)),T,1)
-- P :| (P :-> (not Q))
-- P :| ((not P) :| (not Q))
-- (P :| (not P)) :| (not Q)
-- P :| (not P)
-- T

-- 57  solved with Taut, length = 5
-- Deep: 5
--(P :| ((P :-> Q) :| P),T,1)
-- P :| ((P :-> Q) :| P)
-- P :| (((not P) :| Q) :| P)
-- P :| ((not P) :| (Q :| P))
-- (not P) :| (Q :| P)
-- P :-> (Q :| P)
-- T

-- 62  not solved at wm=9
-- Deep: not solved
--((P :& ((Q :-> P) :<-> P)) :<-> P,T,1)
--     requires these axioms:  (A & B) -> A  -->> A -> B
--                             A -> (B <-> A) ->> A -> B
-- (P :& ((Q :-> P) :<-> P)) :<-> P
-- P :-> ((Q :-> P) :<-> P)
-- P :-> (Q :-> P)
-- P :-> ((not Q) :| P)
-- T

-- 63   takes too long at wm=9
-- Deep: not solved
--(P :| (Q :| ((Q :& R) :<-> P)),T,1)

-- 64  solved with Taut, length = 2
-- Deep: 2
--(P :| ((Q :& Q) :-> Q),T,1)
-- P :| ((Q :& Q) :-> Q)
-- (Q :& Q) :-> Q
-- T

-- 66  solved with Taut, length = 4
-- Deep: 4
--(P :| (P :-> Q),T,1)
-- P :| (P :-> Q)
-- P :| ((not P) :| Q)
-- (P :| (not P)) :| Q
-- P :| (not P)
-- T

-- 67  solved with Taut, length = 1
-- Deep: 1
--(P :-> (P :| Q),T,1)
-- P :-> (P :| Q)
-- T

-- 69  solved with Taut, length = 2
-- Deep: 2
--((not (P :-> Q)) :| (Q :-> Q),T,1)
-- (not (P :-> Q)) :| (Q :-> Q)
-- Q :-> Q
-- T

-- 70  not solved
-- Deep: not solved
-- Shallow: not solved
--(not ((not ((P :-> Q) :& Q)) :& Q),T,1)
--      solution with axiom: (A -> B) & B  -->> B
-- not (not ((P :-> Q) :& Q) :& Q)
-- not (not Q :& Q)
-- not F
-- T

-- 71  solved with Taut, length = 4
-- Deep: 4
--(P :| (P :-> (not (not (Q :<-> Q)))),T,1)
-- P :| (P :-> (not (not (Q :<-> Q))))
-- P :-> (not (not (Q :<-> Q)))
-- P :-> (not (not T))
-- not (not T)
-- T

-- 72  solved with Taut, length = 4
-- Deep: 4
--((P :-> (not Q)) :| P,T,1)
-- (P :-> (not Q)) :| P
-- ((not P) :| (not Q)) :| P
-- (not P) :| ((not Q) :| P)
-- P :-> ((not Q) :| P)
-- T

--76  solved with Taut, length = 4
-- Deep: 4
--((P :-> (not Q)) :| Q,T,1)
-- (P :-> (not Q)) :| Q
-- ((not P) :| (not Q)) :| Q
-- (not (P :& Q)) :| Q
-- (P :& Q) :-> Q
-- T

-- 77  solved with Taut, length = 4
-- Deep: 4
--((not P) :| (Q :-> (P :| P)),T,1)
-- (not P) :| (Q :-> (P :| P))
-- (not P) :| (Q :-> P)
-- P :-> (Q :-> P)
-- P :-> ((not Q) :| P)
-- T




------------------------------------------------------------------------------

-- Not-tautologies
-- 4
--(((P :-> (P :& Q)) :| R) :& R,F,1)

-- 6
-- Shallow: 2
--((P :| P) :& (not P),F,1)

-- 8
--(not (P :<-> ((not Q) :| Q)),F,1)



