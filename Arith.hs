{-
    Occam Agent: Agent.hs
    Complete system of integer arithmetic:
    0#x ==> x
    0+x ==> x
    (x+y) ==> (y+x)
    (0*x) ==> 0
    (1*x) ==> x
    (x*0) ==> 0
    (x*1) ==> x
    x#(y#z) ==> (x+y)#z
    Yet to learn: 
    (x#y)+z ==> x#(y+z)
    x+(y#z) ==> y#(x+z)
    x#(y#z) ==> (x+y)#z
    x#(y#z) ==> (y+x)#z
    x+(y#z) ==> y#(x+z)
    x*(y#z) ==> (x*y)#(x*z)
    (x#y)*z ==> (x*z)#(y*z)
-}
(\v Width) ==> 8
(\v Depth) ==> 10
(\v Axiom) ==> 100
(0 # \x) ==> \x
(0 + \x) ==> \x
(\x + \y) ==> (\y + \x)
(0 * \x) ==> 0
(1 * \x) ==> \x
(\x * 0) ==> 0
(\x * 1) ==> \x
(\y # (\x # \z)) ==> ((\y + \x) # \z)
((\z # \x) + \y) ==> (\z # (\x + \y))
((\x # \y) * \y) ==> ((\x * \y) # (\y * \y))
(0 # 1) ==> 1
(0 + 1) ==> 1
(1 + 1) ==> 2
(1 + 2) ==> 3
(1 + 3) ==> 4
(1 + 4) ==> 5
(1 + 5) ==> 6
(1 + 6) ==> 7
(1 + 7) ==> 8
(1 + 8) ==> 9
(1 + 9) ==> (1 # 0)
(2 + 2) ==> 4
(2 + 3) ==> 5
(2 + 4) ==> 6
(2 + 5) ==> 7
(2 + 6) ==> 8
(2 + 7) ==> 9
(2 + 8) ==> (1 # 0)
(2 + 9) ==> (1 # 1)
(3 + 3) ==> 6
(3 + 4) ==> 7
(3 + 5) ==> 8
(3 + 6) ==> 9
(3 + 7) ==> (1 # 0)
(3 + 8) ==> (1 # 1)
(3 + 9) ==> (1 # 2)
(4 + 4) ==> 8
(4 + 5) ==> 9
(4 + 6) ==> (1 # 0)
(4 + 7) ==> (1 # 1)
(4 + 8) ==> (1 # 2)
(4 + 9) ==> (1 # 3)
(5 + 5) ==> (1 # 0)
(5 + 6) ==> (1 # 1)
(5 + 7) ==> (1 # 2)
(5 + 8) ==> (1 # 3)
(5 + 9) ==> (1 # 4)
(6 + 6) ==> (1 # 2)
(6 + 7) ==> (1 # 3)
(6 + 8) ==> (1 # 4)
(6 + 9) ==> (1 # 5)
(7 + 7) ==> (1 # 4)
(7 + 8) ==> (1 # 5)
(7 + 9) ==> (1 # 6)
(8 + 8) ==> (1 # 6)
(8 + 9) ==> (1 # 7)
(9 + 9) ==> (1 # 8)
(0 * 1) ==> 0
(1 * 0) ==> 0
(2 * 2) ==> 4
(2 * 3) ==> 6
(2 * 4) ==> 8
(2 * 5) ==> (1 # 0)
(2 * 6) ==> (1 # 2)
(2 * 7) ==> (1 # 4)
(2 * 8) ==> (1 # 6)
(2 * 9) ==> (1 # 8)
(3 * 2) ==> 6
(3 * 3) ==> 9
(3 * 4) ==> (1 # 2)
(3 * 5) ==> (1 # 5)
(3 * 6) ==> (1 # 8)
(3 * 7) ==> (2 # 1)
(3 * 8) ==> (2 # 4)
(3 * 9) ==> (2 # 7)
(4 * 2) ==> 8
(4 * 3) ==> (1 # 2)
(4 * 4) ==> (1 # 6)
(4 * 5) ==> (2 # 0)
(4 * 6) ==> (2 # 4)
(4 * 7) ==> (2 # 8)
(4 * 8) ==> (3 # 2)
(4 * 9) ==> (3 # 6)
(5 * 2) ==> (1 # 0)
(5 * 3) ==> (1 # 5)
(5 * 4) ==> (2 # 0)
(5 * 5) ==> (2 # 5)
(5 * 6) ==> (3 # 0)
(5 * 7) ==> (3 # 5)
(5 * 8) ==> (4 # 0)
(5 * 9) ==> (4 # 5)
(6 * 2) ==> (1 # 2)
(6 * 3) ==> (1 # 8)
(6 * 4) ==> (2 # 4)
(6 * 5) ==> (3 # 0)
(6 * 6) ==> (3 # 6)
(6 * 7) ==> (4 # 2)
(6 * 8) ==> (4 # 8)
(6 * 9) ==> (5 # 4)
(7 * 2) ==> (1 # 4)
(7 * 3) ==> (2 # 1)
(7 * 4) ==> (2 # 8)
(7 * 5) ==> (3 # 5)
(7 * 6) ==> (4 # 2)
(7 * 7) ==> (4 # 9)
(7 * 8) ==> (5 # 6)
(7 * 9) ==> (6 # 3)
(8 * 2) ==> (1 # 6)
(8 * 3) ==> (2 # 4)
(8 * 4) ==> (3 # 2)
(8 * 5) ==> (4 # 0)
(8 * 6) ==> (4 # 8)
(8 * 7) ==> (5 # 6)
(8 * 8) ==> (6 # 4)
(8 * 9) ==> (7 # 2)
(9 * 2) ==> (1 # 8)
(9 * 3) ==> (2 # 7)
(9 * 4) ==> (3 # 6)
(9 * 5) ==> (4 # 5)
(9 * 6) ==> (5 # 4)
(9 * 7) ==> (6 # 3)
(9 * 8) ==> (7 # 2)
(9 * 9) ==> (8 # 1)
((\x # \y) * \z) ==> ((\x * \z) # (\y * \z))
(C,2,1,215,2014-08-10 12:08:29.6025985 UTC,2014-08-13 10:26:01.8805173 UTC,#)
(C,2,1,114,2014-08-10 12:28:42.3613056 UTC,2014-08-13 10:26:01.8805173 UTC,*)
(C,0,1,133,2014-08-10 12:24:09.9658761 UTC,2014-08-13 10:26:01.8805173 UTC,3)
(C,0,1,84,2014-08-10 12:24:20.2556249 UTC,2014-08-13 10:26:01.8805173 UTC,5)
(C,0,1,16,2014-08-12 09:13:38.7061727 UTC,2014-08-13 10:26:01.8805173 UTC,(5 # 3))
(C,0,1,16,2014-08-12 09:13:38.7061727 UTC,2014-08-13 10:26:01.8805173 UTC,((5 # 3) # 6))
(C,0,1,83,2014-08-10 12:24:32.6530666 UTC,2014-08-13 10:26:01.8805173 UTC,8)
(C,0,1,100,2014-08-10 12:24:29.2809592 UTC,2014-08-13 10:26:01.8805173 UTC,7)
(C,0,1,111,2014-08-10 12:24:25.5268185 UTC,2014-08-13 10:26:01.8805173 UTC,6)
(C,0,0,14,2014-08-12 09:13:38.7061727 UTC,2014-08-13 10:26:01.8805173 UTC,(6 # 7))
(C,0,0,14,2014-08-12 09:13:38.7061727 UTC,2014-08-13 10:26:01.8805173 UTC,((6 # 7) * 8))
(C,0,1,138,2014-08-10 12:08:29.6025985 UTC,2014-08-13 09:49:53.3904037 UTC,1)
(C,0,1,44,2014-08-10 12:08:29.6025985 UTC,2014-08-13 09:49:53.3904037 UTC,0)
(C,0,0,4,2014-08-10 12:08:29.6025985 UTC,2014-08-13 09:49:53.3904037 UTC,(0 # 1))
(C,0,1,4,2014-08-12 10:57:03.1375579 UTC,2014-08-12 10:57:17.4797768 UTC,((7 # 9) # 0))
(C,0,1,18,2014-08-10 12:24:39.2487124 UTC,2014-08-12 10:57:17.4797768 UTC,(1 # 0))
(C,0,1,64,2014-08-10 12:24:36.0003231 UTC,2014-08-12 10:57:17.4797768 UTC,9)
(C,0,1,5,2014-08-12 10:56:34.7504917 UTC,2014-08-12 10:57:17.4797768 UTC,(7 # 9))
(C,0,0,4,2014-08-12 10:57:03.1375579 UTC,2014-08-12 10:57:17.4797768 UTC,((7 # 9) * (1 # 0)))
(C,0,1,125,2014-08-10 12:08:57.1192381 UTC,2014-08-12 10:56:34.7504917 UTC,2)
(C,0,1,3,2014-08-10 12:35:49.7787394 UTC,2014-08-12 10:56:34.7504917 UTC,(6 # 3))
(C,0,1,1,2014-08-12 10:56:34.7504917 UTC,2014-08-12 10:56:34.7504917 UTC,((6 # 3) # 2))
(C,0,0,1,2014-08-12 10:56:34.7504917 UTC,2014-08-12 10:56:34.7504917 UTC,((7 # 9) * 8))
(C,0,0,5,2014-08-10 12:33:45.7715407 UTC,2014-08-12 10:50:34.3370873 UTC,(3 * 3))
(C,0,0,2,2014-08-12 10:50:32.5813734 UTC,2014-08-12 10:50:34.3370873 UTC,(1 * 3))
(C,0,0,2,2014-08-12 10:50:32.5813734 UTC,2014-08-12 10:50:34.3370873 UTC,((1 * 3) # (3 * 3)))
(C,0,1,4,2014-08-12 10:50:01.9041176 UTC,2014-08-12 10:50:04.3531743 UTC,(6 # 9))
(C,0,0,3,2014-08-10 12:33:20.6215647 UTC,2014-08-12 10:50:04.3531743 UTC,(2 * 3))
(C,0,0,2,2014-08-12 10:50:01.9041176 UTC,2014-08-12 10:50:04.3531743 UTC,((2 * 3) # (3 * 3)))
(C,0,1,10,2014-08-12 09:18:12.1382646 UTC,2014-08-12 10:50:04.3531743 UTC,(2 # 3))
(C,0,0,2,2014-08-12 10:50:01.9041176 UTC,2014-08-12 10:50:04.3531743 UTC,((2 # 3) * 3))
(C,0,1,2,2014-08-12 09:28:54.8875465 UTC,2014-08-12 09:29:45.4748126 UTC,((2 # 6) # 6))
(C,0,0,2,2014-08-10 12:25:23.1165834 UTC,2014-08-12 09:29:45.4748126 UTC,(3 + 2))
(C,0,0,3,2014-08-12 09:28:54.8875465 UTC,2014-08-12 09:29:45.4748126 UTC,((2 # 3) # 4))
(C,0,0,1,2014-08-12 09:29:45.4748126 UTC,2014-08-12 09:29:45.4748126 UTC,(((2 # 3) # 4) + (3 + 2)))
(C,0,1,4,2014-08-10 12:34:29.8478026 UTC,2014-08-12 09:28:54.8875465 UTC,(3 # 2))
(C,0,0,1,2014-08-12 09:28:54.8875465 UTC,2014-08-12 09:28:54.8875465 UTC,(((2 # 3) # 4) + (3 # 2)))
(C,0,1,1,2014-08-12 09:27:16.4735883 UTC,2014-08-12 09:27:16.4735883 UTC,((1 # 0) # 1))
(C,0,0,1,2014-08-12 09:27:16.4735883 UTC,2014-08-12 09:27:16.4735883 UTC,((9 # 9) + 2))
(C,0,1,1,2014-08-12 09:26:33.1209948 UTC,2014-08-12 09:26:33.1209948 UTC,(9 # 6))
(C,0,0,1,2014-08-12 09:26:33.1209948 UTC,2014-08-12 09:26:33.1209948 UTC,(2 # 2))
(C,0,0,1,2014-08-12 09:26:33.1209948 UTC,2014-08-12 09:26:33.1209948 UTC,((7 # 4) + (2 # 2)))
(C,0,1,1,2014-08-12 09:25:36.038569 UTC,2014-08-12 09:25:36.038569 UTC,(4 # 6))
(C,0,1,3,2014-08-10 12:35:17.6691442 UTC,2014-08-12 09:24:56.1693261 UTC,(4 # 2))
(C,0,0,1,2014-08-12 09:24:56.1693261 UTC,2014-08-12 09:24:56.1693261 UTC,((3 # 4) + 8))
(C,0,1,3,2014-08-10 12:34:49.1818543 UTC,2014-08-12 09:24:10.8162153 UTC,(3 # 0))
(C,0,0,1,2014-08-12 09:24:10.8162153 UTC,2014-08-12 09:24:10.8162153 UTC,((2 # 3) + 7))
(C,0,1,5,2014-08-12 09:22:42.101464 UTC,2014-08-12 09:23:01.2224952 UTC,(5 # 5))
(C,0,0,3,2014-08-12 09:22:48.3457338 UTC,2014-08-12 09:23:01.2224952 UTC,((5 # 2) + 3))
(C,0,0,3,2014-08-10 12:25:30.0793887 UTC,2014-08-12 09:18:25.3411715 UTC,(3 + 4))
(C,0,0,2,2014-08-12 09:18:21.0436477 UTC,2014-08-12 09:18:25.3411715 UTC,(2 # (3 + 4)))
(C,0,1,5,2014-08-10 12:39:53.3678907 UTC,2014-08-10 12:41:14.1445531 UTC,(7 # 7))
(C,0,0,3,2014-08-10 12:26:52.4129043 UTC,2014-08-10 12:41:14.1445531 UTC,(6 + 1))
(C,0,0,2,2014-08-10 12:41:08.9738079 UTC,2014-08-10 12:41:14.1445531 UTC,((6 + 1) # 7))
(C,0,0,3,2014-08-10 12:39:53.3678907 UTC,2014-08-10 12:40:06.1329542 UTC,(6 # (1 # 7)))
(C,0,1,2,2014-08-10 12:36:11.6154507 UTC,2014-08-10 12:36:35.5672553 UTC,(7 # 2))
(C,0,0,1,2014-08-10 12:36:35.5672553 UTC,2014-08-10 12:36:35.5672553 UTC,(9 * 8))
(C,0,1,2,2014-08-10 12:35:23.4544543 UTC,2014-08-10 12:36:29.1806556 UTC,(5 # 4))
(C,0,0,1,2014-08-10 12:36:29.1806556 UTC,2014-08-10 12:36:29.1806556 UTC,(9 * 6))
(C,0,1,4,2014-08-10 12:34:33.1584127 UTC,2014-08-10 12:36:22.7969651 UTC,(3 # 6))
(C,0,0,2,2014-08-10 12:36:19.8075815 UTC,2014-08-10 12:36:22.7969651 UTC,(9 * 4))
(C,0,0,1,2014-08-10 12:36:17.2664029 UTC,2014-08-10 12:36:17.2664029 UTC,(9 * 3))
(C,0,0,1,2014-08-10 12:36:11.6154507 UTC,2014-08-10 12:36:11.6154507 UTC,(8 * 9))
(C,0,1,2,2014-08-10 12:35:47.1057783 UTC,2014-08-10 12:36:06.2930694 UTC,(5 # 6))
(C,0,0,1,2014-08-10 12:36:06.2930694 UTC,2014-08-10 12:36:06.2930694 UTC,(8 * 7))
(C,0,1,2,2014-08-10 12:34:55.3350524 UTC,2014-08-10 12:36:00.7747086 UTC,(4 # 0))
(C,0,0,1,2014-08-10 12:36:00.7747086 UTC,2014-08-10 12:36:00.7747086 UTC,(8 * 5))
(C,0,1,4,2014-08-10 12:34:01.9988923 UTC,2014-08-10 12:35:55.5031037 UTC,(2 # 4))
(C,0,0,1,2014-08-10 12:35:55.5031037 UTC,2014-08-10 12:35:55.5031037 UTC,(8 * 3))
(C,0,0,1,2014-08-10 12:35:49.7787394 UTC,2014-08-10 12:35:49.7787394 UTC,(7 * 9))
(C,0,1,1,2014-08-10 12:35:44.4558267 UTC,2014-08-10 12:35:44.4558267 UTC,(4 # 9))
(C,0,0,1,2014-08-10 12:35:44.4558267 UTC,2014-08-10 12:35:44.4558267 UTC,(7 * 7))
(C,0,1,2,2014-08-10 12:34:52.3974636 UTC,2014-08-10 12:35:38.664687 UTC,(3 # 5))
(C,0,0,1,2014-08-10 12:35:38.664687 UTC,2014-08-10 12:35:38.664687 UTC,(7 * 5))
(C,0,1,2,2014-08-10 12:33:59.1922522 UTC,2014-08-10 12:35:33.0910278 UTC,(2 # 1))
(C,0,0,1,2014-08-10 12:35:33.0910278 UTC,2014-08-10 12:35:33.0910278 UTC,(7 * 3))
(C,0,0,1,2014-08-10 12:35:23.4544543 UTC,2014-08-10 12:35:23.4544543 UTC,(6 * 9))
(C,0,0,1,2014-08-10 12:35:17.6691442 UTC,2014-08-10 12:35:17.6691442 UTC,(6 * 7))
(C,0,0,1,2014-08-10 12:35:11.1507544 UTC,2014-08-10 12:35:11.1507544 UTC,(6 * 5))
(C,0,0,1,2014-08-10 12:35:04.6614099 UTC,2014-08-10 12:35:04.6614099 UTC,(6 * 3))
(C,0,0,1,2014-08-10 12:34:58.2825683 UTC,2014-08-10 12:34:58.2825683 UTC,(5 * 9))
(C,0,0,1,2014-08-10 12:34:52.3974636 UTC,2014-08-10 12:34:52.3974636 UTC,(5 * 7))
(C,0,0,1,2014-08-10 12:34:46.3159283 UTC,2014-08-10 12:34:46.3159283 UTC,(5 * 5))
(C,0,1,6,2014-08-10 12:27:15.0715418 UTC,2014-08-10 12:34:41.0004259 UTC,(1 # 5))
(C,0,0,1,2014-08-10 12:34:41.0004259 UTC,2014-08-10 12:34:41.0004259 UTC,(5 * 3))
(C,0,0,1,2014-08-10 12:34:33.1584127 UTC,2014-08-10 12:34:33.1584127 UTC,(4 * 9))
(C,0,0,1,2014-08-10 12:34:27.0729399 UTC,2014-08-10 12:34:27.0729399 UTC,(4 * 7))
(C,0,0,1,2014-08-10 12:34:20.8612194 UTC,2014-08-10 12:34:20.8612194 UTC,(4 * 5))
(C,0,0,1,2014-08-10 12:34:14.7898668 UTC,2014-08-10 12:34:14.7898668 UTC,(4 * 3))
(C,0,0,1,2014-08-10 12:34:05.1029601 UTC,2014-08-10 12:34:05.1029601 UTC,(3 * 9))
(C,0,0,1,2014-08-10 12:33:59.1922522 UTC,2014-08-10 12:33:59.1922522 UTC,(3 * 7))
(C,0,0,1,2014-08-10 12:33:52.0032473 UTC,2014-08-10 12:33:52.0032473 UTC,(3 * 5))
(C,0,0,1,2014-08-10 12:33:39.5742093 UTC,2014-08-10 12:33:39.5742093 UTC,(2 * 9))
(C,0,0,1,2014-08-10 12:33:33.4100819 UTC,2014-08-10 12:33:33.4100819 UTC,(2 * 7))
(C,0,0,1,2014-08-10 12:33:27.1427399 UTC,2014-08-10 12:33:27.1427399 UTC,(2 * 5))
(C,0,0,1,2014-08-10 12:33:12.3928659 UTC,2014-08-10 12:33:12.3928659 UTC,(2 * 1))
(C,0,0,1,2014-08-10 12:33:02.8560011 UTC,2014-08-10 12:33:02.8560011 UTC,(1 * 1))
(C,0,0,1,2014-08-10 12:28:46.1006482 UTC,2014-08-10 12:28:46.1006482 UTC,(0 * 2))
(C,0,0,1,2014-08-10 12:28:38.1134173 UTC,2014-08-10 12:28:38.1134173 UTC,(9 + 9))
(C,0,0,1,2014-08-10 12:28:33.093463 UTC,2014-08-10 12:28:33.093463 UTC,(9 + 7))
(C,0,0,1,2014-08-10 12:28:27.9072229 UTC,2014-08-10 12:28:27.9072229 UTC,(9 + 5))
(C,0,0,1,2014-08-10 12:28:22.4327111 UTC,2014-08-10 12:28:22.4327111 UTC,(9 + 3))
(C,0,0,1,2014-08-10 12:28:16.8763715 UTC,2014-08-10 12:28:16.8763715 UTC,(9 + 1))
(C,0,0,1,2014-08-10 12:28:09.6905676 UTC,2014-08-10 12:28:09.6905676 UTC,(8 + 8))
(C,0,0,1,2014-08-10 12:28:04.3480751 UTC,2014-08-10 12:28:04.3480751 UTC,(8 + 6))
(C,0,0,1,2014-08-10 12:27:57.5457866 UTC,2014-08-10 12:27:57.5457866 UTC,(8 + 4))
(C,0,0,1,2014-08-10 12:27:52.2394544 UTC,2014-08-10 12:27:52.2394544 UTC,(8 + 2))
(C,0,0,1,2014-08-10 12:27:41.8859695 UTC,2014-08-10 12:27:41.8859695 UTC,(7 + 9))
(C,0,0,1,2014-08-10 12:27:34.0791865 UTC,2014-08-10 12:27:34.0791865 UTC,(7 + 7))
(C,0,0,1,2014-08-10 12:27:29.0179436 UTC,2014-08-10 12:27:29.0179436 UTC,(7 + 5))
(C,0,0,1,2014-08-10 12:27:23.5096066 UTC,2014-08-10 12:27:23.5096066 UTC,(7 + 3))
(C,0,0,1,2014-08-10 12:27:18.1454833 UTC,2014-08-10 12:27:18.1454833 UTC,(7 + 1))
(C,0,0,1,2014-08-10 12:27:12.0939566 UTC,2014-08-10 12:27:12.0939566 UTC,(6 + 8))
(C,0,0,1,2014-08-10 12:27:06.228477 UTC,2014-08-10 12:27:06.228477 UTC,(6 + 6))
(C,0,0,1,2014-08-10 12:27:00.7671867 UTC,2014-08-10 12:27:00.7671867 UTC,(6 + 4))
(C,0,0,1,2014-08-10 12:26:48.9687269 UTC,2014-08-10 12:26:48.9687269 UTC,(5 + 9))
(C,0,0,1,2014-08-10 12:26:42.5101193 UTC,2014-08-10 12:26:42.5101193 UTC,(5 + 7))
(C,0,0,1,2014-08-10 12:26:36.2053193 UTC,2014-08-10 12:26:36.2053193 UTC,(5 + 5))
(C,0,0,1,2014-08-10 12:26:19.8275648 UTC,2014-08-10 12:26:19.8275648 UTC,(5 + 1))
(C,0,0,1,2014-08-10 12:26:13.3606626 UTC,2014-08-10 12:26:13.3606626 UTC,(4 + 8))
(C,0,0,1,2014-08-10 12:26:07.1013818 UTC,2014-08-10 12:26:07.1013818 UTC,(4 + 6))
(C,0,0,1,2014-08-10 12:25:58.4488923 UTC,2014-08-10 12:25:58.4488923 UTC,(4 + 4))
(C,0,0,1,2014-08-10 12:25:52.7787656 UTC,2014-08-10 12:25:52.7787656 UTC,(4 + 2))
(C,0,0,1,2014-08-10 12:25:46.628819 UTC,2014-08-10 12:25:46.628819 UTC,(3 + 9))
(C,0,0,1,2014-08-10 12:25:40.3945185 UTC,2014-08-10 12:25:40.3945185 UTC,(3 + 7))
(C,0,0,1,2014-08-10 12:25:33.9336074 UTC,2014-08-10 12:25:33.9336074 UTC,(3 + 5))
(C,0,0,1,2014-08-10 12:25:25.7125873 UTC,2014-08-10 12:25:25.7125873 UTC,(3 + 3))
(C,0,0,1,2014-08-10 12:25:19.5525861 UTC,2014-08-10 12:25:19.5525861 UTC,(3 + 1))
(C,0,0,1,2014-08-10 12:25:09.4402026 UTC,2014-08-10 12:25:09.4402026 UTC,(2 + 8))
(C,0,0,1,2014-08-10 12:25:03.2233502 UTC,2014-08-10 12:25:03.2233502 UTC,(2 + 6))
(C,0,0,1,2014-08-10 12:24:56.9647539 UTC,2014-08-10 12:24:56.9647539 UTC,(2 + 4))
(C,0,0,1,2014-08-10 12:24:50.1112515 UTC,2014-08-10 12:24:50.1112515 UTC,(2 + 2))
(C,0,0,1,2014-08-10 12:24:42.73217 UTC,2014-08-10 12:24:42.73217 UTC,(2 + 0))
(C,0,0,1,2014-08-10 12:24:36.0003231 UTC,2014-08-10 12:24:36.0003231 UTC,(1 + 8))
(C,0,0,1,2014-08-10 12:24:29.2809592 UTC,2014-08-10 12:24:29.2809592 UTC,(1 + 6))
(C,0,0,1,2014-08-10 12:24:20.2556249 UTC,2014-08-10 12:24:20.2556249 UTC,(1 + 4))
(C,0,0,1,2014-08-10 12:24:09.9658761 UTC,2014-08-10 12:24:09.9658761 UTC,(1 + 2))
(C,0,0,2,2014-08-10 12:23:24.7310922 UTC,2014-08-10 12:23:48.0681446 UTC,(1 + 0))
(C,0,0,2,2014-08-10 12:09:28.3039796 UTC,2014-08-10 12:09:34.7746862 UTC,(0 + 1))
(C,0,0,2,2014-08-10 12:08:57.1192381 UTC,2014-08-10 12:09:01.3779398 UTC,(0 # 2))
(C,0,0,3,2014-08-10 12:09:43.609877 UTC,2014-08-10 12:09:53.7451199 UTC,(0 + 2))
(C,0,0,1,2014-08-10 12:23:59.3785978 UTC,2014-08-10 12:23:59.3785978 UTC,(1 + 1))
(C,0,0,1,2014-08-10 12:24:15.309889 UTC,2014-08-10 12:24:15.309889 UTC,(1 + 3))
(C,0,0,1,2014-08-10 12:24:25.5268185 UTC,2014-08-10 12:24:25.5268185 UTC,(1 + 5))
(C,0,0,1,2014-08-10 12:24:32.6530666 UTC,2014-08-10 12:24:32.6530666 UTC,(1 + 7))
(C,0,0,1,2014-08-10 12:24:39.2487124 UTC,2014-08-10 12:24:39.2487124 UTC,(1 + 9))
(C,0,0,1,2014-08-10 12:24:46.9834956 UTC,2014-08-10 12:24:46.9834956 UTC,(2 + 1))
(C,0,0,1,2014-08-10 12:25:00.1794163 UTC,2014-08-10 12:25:00.1794163 UTC,(2 + 5))
(C,0,0,1,2014-08-10 12:25:06.4225256 UTC,2014-08-10 12:25:06.4225256 UTC,(2 + 7))
(C,0,0,1,2014-08-10 12:25:13.4699594 UTC,2014-08-10 12:25:13.4699594 UTC,(2 + 9))
(C,0,0,1,2014-08-10 12:25:37.197881 UTC,2014-08-10 12:25:37.197881 UTC,(3 + 6))
(C,0,0,1,2014-08-10 12:25:43.4677189 UTC,2014-08-10 12:25:43.4677189 UTC,(3 + 8))
(C,0,0,1,2014-08-10 12:25:49.7797462 UTC,2014-08-10 12:25:49.7797462 UTC,(4 + 1))
(C,0,0,1,2014-08-10 12:25:55.4748556 UTC,2014-08-10 12:25:55.4748556 UTC,(4 + 3))
(C,0,0,1,2014-08-10 12:26:04.1453372 UTC,2014-08-10 12:26:04.1453372 UTC,(4 + 5))
(C,0,0,1,2014-08-10 12:26:10.1232208 UTC,2014-08-10 12:26:10.1232208 UTC,(4 + 7))
(C,0,0,1,2014-08-10 12:26:16.6890738 UTC,2014-08-10 12:26:16.6890738 UTC,(4 + 9))
(C,0,0,1,2014-08-10 12:26:23.2402847 UTC,2014-08-10 12:26:23.2402847 UTC,(5 + 2))
(C,0,0,1,2014-08-10 12:26:39.4831918 UTC,2014-08-10 12:26:39.4831918 UTC,(5 + 6))
(C,0,0,1,2014-08-10 12:26:45.6765391 UTC,2014-08-10 12:26:45.6765391 UTC,(5 + 8))
(C,0,0,1,2014-08-10 12:26:58.215578 UTC,2014-08-10 12:26:58.215578 UTC,(6 + 3))
(C,0,0,1,2014-08-10 12:27:03.6882683 UTC,2014-08-10 12:27:03.6882683 UTC,(6 + 5))
(C,0,0,1,2014-08-10 12:27:09.1203513 UTC,2014-08-10 12:27:09.1203513 UTC,(6 + 7))
(C,0,0,1,2014-08-10 12:27:15.0715418 UTC,2014-08-10 12:27:15.0715418 UTC,(6 + 9))
(C,0,0,1,2014-08-10 12:27:20.8155834 UTC,2014-08-10 12:27:20.8155834 UTC,(7 + 2))
(C,0,0,1,2014-08-10 12:27:26.3019576 UTC,2014-08-10 12:27:26.3019576 UTC,(7 + 4))
(C,0,0,1,2014-08-10 12:27:31.5904952 UTC,2014-08-10 12:27:31.5904952 UTC,(7 + 6))
(C,0,0,1,2014-08-10 12:27:38.2104797 UTC,2014-08-10 12:27:38.2104797 UTC,(7 + 8))
(C,0,0,1,2014-08-10 12:27:48.8190754 UTC,2014-08-10 12:27:48.8190754 UTC,(8 + 1))
(C,0,0,1,2014-08-10 12:27:54.8363592 UTC,2014-08-10 12:27:54.8363592 UTC,(8 + 3))
(C,0,0,1,2014-08-10 12:28:00.1307604 UTC,2014-08-10 12:28:00.1307604 UTC,(8 + 5))
(C,0,0,1,2014-08-10 12:28:07.22919 UTC,2014-08-10 12:28:07.22919 UTC,(8 + 7))
(C,0,0,1,2014-08-10 12:28:13.6049174 UTC,2014-08-10 12:28:13.6049174 UTC,(8 + 9))
(C,0,0,1,2014-08-10 12:28:19.6044 UTC,2014-08-10 12:28:19.6044 UTC,(9 + 2))
(C,0,1,8,2014-08-10 12:25:13.4699594 UTC,2014-08-10 12:28:19.6044 UTC,(1 # 1))
(C,0,0,1,2014-08-10 12:28:25.1267543 UTC,2014-08-10 12:28:25.1267543 UTC,(9 + 4))
(C,0,0,1,2014-08-10 12:28:30.5047917 UTC,2014-08-10 12:28:30.5047917 UTC,(9 + 6))
(C,0,0,1,2014-08-10 12:28:35.578773 UTC,2014-08-10 12:28:35.578773 UTC,(9 + 8))
(C,0,0,1,2014-08-10 12:28:42.3613056 UTC,2014-08-10 12:28:42.3613056 UTC,(0 * 1))
(C,0,0,1,2014-08-10 12:32:59.0765612 UTC,2014-08-10 12:32:59.0765612 UTC,(1 * 0))
(C,0,0,1,2014-08-10 12:33:06.7444175 UTC,2014-08-10 12:33:06.7444175 UTC,(2 * 0))
(C,0,0,1,2014-08-10 12:33:17.043268 UTC,2014-08-10 12:33:17.043268 UTC,(2 * 2))
(C,0,0,1,2014-08-10 12:33:23.8149923 UTC,2014-08-10 12:33:23.8149923 UTC,(2 * 4))
(C,0,0,1,2014-08-10 12:33:30.3355445 UTC,2014-08-10 12:33:30.3355445 UTC,(2 * 6))
(C,0,0,1,2014-08-10 12:33:36.5707701 UTC,2014-08-10 12:33:36.5707701 UTC,(2 * 8))
(C,0,0,1,2014-08-10 12:33:56.1438121 UTC,2014-08-10 12:33:56.1438121 UTC,(3 * 6))
(C,0,0,1,2014-08-10 12:34:01.9988923 UTC,2014-08-10 12:34:01.9988923 UTC,(3 * 8))
(C,0,0,1,2014-08-10 12:34:08.8590028 UTC,2014-08-10 12:34:08.8590028 UTC,(4 * 2))
(C,0,0,1,2014-08-10 12:34:17.8581333 UTC,2014-08-10 12:34:17.8581333 UTC,(4 * 4))
(C,0,0,1,2014-08-10 12:34:24.235142 UTC,2014-08-10 12:34:24.235142 UTC,(4 * 6))
(C,0,0,1,2014-08-10 12:34:29.8478026 UTC,2014-08-10 12:34:29.8478026 UTC,(4 * 8))
(C,0,0,1,2014-08-10 12:34:36.667409 UTC,2014-08-10 12:34:36.667409 UTC,(5 * 2))
(C,0,0,1,2014-08-10 12:34:43.7221914 UTC,2014-08-10 12:34:43.7221914 UTC,(5 * 4))
(C,0,1,2,2014-08-10 12:34:20.8612194 UTC,2014-08-10 12:34:43.7221914 UTC,(2 # 0))
(C,0,0,1,2014-08-10 12:34:49.1818543 UTC,2014-08-10 12:34:49.1818543 UTC,(5 * 6))
(C,0,0,1,2014-08-10 12:34:55.3350524 UTC,2014-08-10 12:34:55.3350524 UTC,(5 * 8))
(C,0,0,1,2014-08-10 12:35:01.3963256 UTC,2014-08-10 12:35:01.3963256 UTC,(6 * 2))
(C,0,0,1,2014-08-10 12:35:07.9547544 UTC,2014-08-10 12:35:07.9547544 UTC,(6 * 4))
(C,0,0,1,2014-08-10 12:35:14.2101804 UTC,2014-08-10 12:35:14.2101804 UTC,(6 * 6))
(C,0,0,1,2014-08-10 12:35:30.0180309 UTC,2014-08-10 12:35:30.0180309 UTC,(7 * 2))
(C,0,1,7,2014-08-10 12:26:48.9687269 UTC,2014-08-10 12:35:30.0180309 UTC,(1 # 4))
(C,0,0,1,2014-08-10 12:35:35.8438054 UTC,2014-08-10 12:35:35.8438054 UTC,(7 * 4))
(C,0,1,2,2014-08-10 12:34:27.0729399 UTC,2014-08-10 12:35:35.8438054 UTC,(2 # 8))
(C,0,0,1,2014-08-10 12:35:41.6227545 UTC,2014-08-10 12:35:41.6227545 UTC,(7 * 6))
(C,0,0,1,2014-08-10 12:35:52.7803024 UTC,2014-08-10 12:35:52.7803024 UTC,(8 * 2))
(C,0,1,6,2014-08-10 12:27:41.8859695 UTC,2014-08-10 12:35:52.7803024 UTC,(1 # 6))
(C,0,0,1,2014-08-10 12:35:58.0570626 UTC,2014-08-10 12:35:58.0570626 UTC,(8 * 4))
(C,0,0,1,2014-08-10 12:36:03.4910924 UTC,2014-08-10 12:36:03.4910924 UTC,(8 * 6))
(C,0,0,1,2014-08-10 12:36:09.1256429 UTC,2014-08-10 12:36:09.1256429 UTC,(8 * 8))
(C,0,1,1,2014-08-10 12:36:09.1256429 UTC,2014-08-10 12:36:09.1256429 UTC,(6 # 4))
(C,0,0,1,2014-08-10 12:36:14.5879862 UTC,2014-08-10 12:36:14.5879862 UTC,(9 * 2))
(C,0,1,5,2014-08-10 12:28:38.1134173 UTC,2014-08-10 12:36:14.5879862 UTC,(1 # 8))
(C,0,0,1,2014-08-10 12:36:25.8929072 UTC,2014-08-10 12:36:25.8929072 UTC,(9 * 5))
(C,0,1,2,2014-08-10 12:34:58.2825683 UTC,2014-08-10 12:36:25.8929072 UTC,(4 # 5))
(C,0,0,1,2014-08-10 12:36:32.3024797 UTC,2014-08-10 12:36:32.3024797 UTC,(9 * 7))
(C,0,0,1,2014-08-10 12:36:38.7776267 UTC,2014-08-10 12:36:38.7776267 UTC,(9 * 9))
(C,0,1,1,2014-08-10 12:36:38.7776267 UTC,2014-08-10 12:36:38.7776267 UTC,(8 # 1))
(C,0,0,3,2014-08-10 12:41:36.5428933 UTC,2014-08-10 12:41:40.5666734 UTC,((6 + 2) # 7))
(C,0,0,4,2014-08-10 12:26:55.5210403 UTC,2014-08-10 12:41:40.5666734 UTC,(6 + 2))
(C,0,0,4,2014-08-10 12:40:27.7175115 UTC,2014-08-10 12:43:48.3907104 UTC,(6 # (2 # 7)))
(C,0,1,7,2014-08-10 12:40:27.7175115 UTC,2014-08-10 12:43:48.3907104 UTC,(8 # 7))
(C,0,0,12,2014-08-10 12:42:04.9773382 UTC,2014-08-12 09:10:56.9062536 UTC,(3 # (1 # 7)))
(C,0,0,2,2014-08-12 09:16:29.3875033 UTC,2014-08-12 09:16:32.8058893 UTC,(6 # (5 + 3)))
(C,0,0,3,2014-08-10 12:26:26.0851291 UTC,2014-08-12 09:16:32.8058893 UTC,(5 + 3))
(C,0,0,3,2014-08-12 09:18:12.1382646 UTC,2014-08-12 09:18:31.2202622 UTC,((2 # 3) + 4))
(C,0,1,11,2014-08-10 12:34:05.1029601 UTC,2014-08-12 09:18:31.2202622 UTC,(2 # 7))
(C,0,0,2,2014-08-12 09:19:27.4687001 UTC,2014-08-12 09:19:28.4410385 UTC,(2 # (5 + 4)))
(C,0,0,3,2014-08-10 12:26:29.0559606 UTC,2014-08-12 09:19:28.4410385 UTC,(5 + 4))
(C,0,0,2,2014-08-12 09:19:36.0421917 UTC,2014-08-12 09:19:38.2349688 UTC,((2 # 5) + 4))
(C,0,1,3,2014-08-10 12:34:46.3159283 UTC,2014-08-12 09:19:38.2349688 UTC,(2 # 5))
(C,0,1,4,2014-08-12 09:19:27.4687001 UTC,2014-08-12 09:19:38.2349688 UTC,(2 # 9))
(C,0,0,2,2014-08-12 09:20:22.1405709 UTC,2014-08-12 09:20:22.9038366 UTC,(6 # (2 + 3)))
(C,0,0,2,2014-08-12 09:20:28.2089005 UTC,2014-08-12 09:20:30.0405489 UTC,((6 # 2) + 3))
(C,0,0,2,2014-08-12 09:20:28.2089005 UTC,2014-08-12 09:20:30.0405489 UTC,(6 # 2))
(C,0,0,2,2014-08-12 09:22:42.101464 UTC,2014-08-12 09:22:42.9767751 UTC,(5 # (2 + 3)))
(C,0,0,6,2014-08-10 12:24:53.6902744 UTC,2014-08-12 09:22:42.9767751 UTC,(2 + 3))
(C,0,0,3,2014-08-12 09:16:04.4284505 UTC,2014-08-12 09:23:09.6684933 UTC,((6 # 5) + 3))
(C,0,1,7,2014-08-12 09:16:04.4284505 UTC,2014-08-12 09:23:09.6684933 UTC,(6 # 5))
(C,0,1,5,2014-08-12 09:16:04.4284505 UTC,2014-08-12 09:23:09.6684933 UTC,(6 # 8))
(C,0,0,1,2014-08-12 09:24:27.6181839 UTC,2014-08-12 09:24:27.6181839 UTC,((2 # 3) + 8))
(C,0,1,1,2014-08-12 09:24:27.6181839 UTC,2014-08-12 09:24:27.6181839 UTC,(3 # 1))
(C,0,0,1,2014-08-12 09:25:23.8602454 UTC,2014-08-12 09:25:23.8602454 UTC,((3 # 4) + (1 # 0)))
(C,0,1,1,2014-08-12 09:25:23.8602454 UTC,2014-08-12 09:25:23.8602454 UTC,(4 # 4))
(C,0,0,2,2014-08-12 09:25:36.038569 UTC,2014-08-12 09:26:06.7012584 UTC,((3 # 4) + (1 # 2)))
(C,0,0,4,2014-08-12 09:24:56.1693261 UTC,2014-08-12 09:26:06.7012584 UTC,(3 # 4))
(C,0,1,13,2014-08-10 12:25:46.628819 UTC,2014-08-12 09:26:06.7012584 UTC,(1 # 2))
(C,0,1,13,2014-08-10 12:42:04.9773382 UTC,2014-08-12 09:26:06.7012584 UTC,(4 # 7))
(C,0,0,1,2014-08-12 09:26:52.6029165 UTC,2014-08-12 09:26:52.6029165 UTC,((7 # 4) + (3 # 2)))
(C,0,0,2,2014-08-12 09:26:33.1209948 UTC,2014-08-12 09:26:52.6029165 UTC,(7 # 4))
(C,0,1,1,2014-08-12 09:26:52.6029165 UTC,2014-08-12 09:26:52.6029165 UTC,((1 # 0) # 6))
(C,0,0,1,2014-08-12 09:28:05.5750275 UTC,2014-08-12 09:28:05.5750275 UTC,((9 # 9) + (7 # 8)))
(C,0,0,2,2014-08-12 09:27:16.4735883 UTC,2014-08-12 09:28:05.5750275 UTC,(9 # 9))
(C,0,0,1,2014-08-12 09:28:05.5750275 UTC,2014-08-12 09:28:05.5750275 UTC,(7 # 8))
(C,0,1,1,2014-08-12 09:28:05.5750275 UTC,2014-08-12 09:28:05.5750275 UTC,((1 # 7) # 7))
(C,0,1,18,2014-08-10 12:28:13.6049174 UTC,2014-08-12 09:28:05.5750275 UTC,(1 # 7))
(C,0,0,1,2014-08-12 09:29:10.0859893 UTC,2014-08-12 09:29:10.0859893 UTC,(((2 # 3) # 4) + 3))
(C,0,1,1,2014-08-12 09:29:10.0859893 UTC,2014-08-12 09:29:10.0859893 UTC,((2 # 3) # 7))
(C,0,0,1,2014-08-12 10:51:34.950284 UTC,2014-08-12 10:51:34.950284 UTC,(((6 * 8) # 0) + (7 * 8)))
(C,0,0,1,2014-08-12 10:51:34.950284 UTC,2014-08-12 10:51:34.950284 UTC,((6 * 8) # 0))
(C,0,1,3,2014-08-12 09:13:51.5997519 UTC,2014-08-12 10:51:34.950284 UTC,(((4 # 8) + 5) # 6))
(C,0,1,3,2014-08-12 09:13:51.5997519 UTC,2014-08-12 10:51:34.950284 UTC,((4 # 8) + 5))
(C,0,1,5,2014-08-10 12:35:20.6633823 UTC,2014-08-12 10:51:34.950284 UTC,(4 # 8))
(C,2,1,134,2014-08-10 12:09:28.3039796 UTC,2014-08-12 10:51:34.950284 UTC,+)
(C,0,1,2,2014-08-12 10:52:36.7194138 UTC,2014-08-12 10:53:34.6761444 UTC,((6 * 8) # (7 * 8)))
(C,0,1,4,2014-08-10 12:35:20.6633823 UTC,2014-08-12 10:53:34.6761444 UTC,(6 * 8))
(C,0,1,4,2014-08-10 12:35:47.1057783 UTC,2014-08-12 10:53:34.6761444 UTC,(7 * 8))
(C,0,0,3,2014-08-12 10:50:32.5813734 UTC,2014-08-12 10:54:02.6095029 UTC,((1 # 3) * 3))
(C,0,1,5,2014-08-12 10:50:32.5813734 UTC,2014-08-12 10:54:02.6095029 UTC,(3 # 9))
(C,0,0,5,2014-08-12 10:49:08.846149 UTC,2014-08-12 10:55:07.803983 UTC,((1 # 3) * 2))
(C,0,0,4,2014-08-12 10:49:08.846149 UTC,2014-08-12 10:55:07.803983 UTC,((1 * 2) # (3 * 2)))
(C,0,0,4,2014-08-12 10:49:08.846149 UTC,2014-08-12 10:55:07.803983 UTC,(1 * 2))
(C,0,0,5,2014-08-10 12:33:42.7799844 UTC,2014-08-12 10:55:07.803983 UTC,(3 * 2))
(C,0,1,11,2014-08-12 09:28:54.8875465 UTC,2014-08-12 10:55:07.803983 UTC,(2 # 6))
(C,0,0,2,2014-08-12 10:55:26.313549 UTC,2014-08-12 10:55:30.0860685 UTC,((1 # 3) * 4))
(C,0,1,16,2014-08-10 12:26:16.6890738 UTC,2014-08-12 10:55:30.0860685 UTC,(1 # 3))
(C,0,0,2,2014-08-12 10:55:26.313549 UTC,2014-08-12 10:55:30.0860685 UTC,((1 * 4) # (3 * 4)))
(C,0,0,2,2014-08-12 10:55:26.313549 UTC,2014-08-12 10:55:30.0860685 UTC,(1 * 4))
(C,0,1,95,2014-08-10 12:24:15.309889 UTC,2014-08-12 10:55:30.0860685 UTC,4)
(C,0,0,3,2014-08-10 12:33:48.9087364 UTC,2014-08-12 10:55:30.0860685 UTC,(3 * 4))
(C,0,1,7,2014-08-12 09:22:48.3457338 UTC,2014-08-12 10:55:30.0860685 UTC,(5 # 2))
(S,10,16,2014-08-12 09:13:38.712176 UTC,2014-08-13 10:26:01.8865187 UTC,((\x # \y) * \z),[((10,(5 # 2)),1),((10,((5 # 3) # 6)),6),((27,(5 # 2)),2),((27,((5 # 3) # 6)),8)])
(S,1,6,2014-08-10 12:08:29.6125957 UTC,2014-08-13 09:49:53.3914021 UTC,(\x # \y),[((1,1),3),((1,2),1),((2,1),2),((3,1),2),((25,1),2),((26,1),2)])
(S,23,6,2014-08-12 10:49:08.8521514 UTC,2014-08-12 10:56:34.7574948 UTC,((\x # \z) * \y),[((23,((6 # 3) # 2)),1),((24,(2 # 6)),4),((24,((6 # 3) # 2)),1)])
(S,27,3,2014-08-12 10:52:36.7254176 UTC,2014-08-12 10:55:30.0930707 UTC,((\x * \z) # (\y * \z)),[((10,(5 # 2)),1),((27,(5 # 2)),2)])
(S,24,4,2014-08-12 10:49:08.8521514 UTC,2014-08-12 10:55:07.8089744 UTC,((\x * \y) # (\z * \y)),[((24,(2 # 6)),3)])
(S,25,5,2014-08-12 10:50:01.9101288 UTC,2014-08-12 10:54:02.6155053 UTC,((\x # \y) * \y),[((25,(3 # 9)),2),((26,(3 # 9)),3),((26,(6 # 9)),1)])
(S,26,4,2014-08-12 10:50:01.9101288 UTC,2014-08-12 10:50:34.3420923 UTC,((\x * \y) # (\y * \y)),[((25,(3 # 9)),1),((26,(3 # 9)),2),((26,(6 # 9)),1)])
(S,22,1,2014-08-12 09:29:10.0919972 UTC,2014-08-12 09:29:10.0919972 UTC,(((\x # \y) # \z) + \y),[])
(S,21,1,2014-08-12 09:28:05.5800324 UTC,2014-08-12 09:28:05.5800324 UTC,((\z # \z) + (\x # \y)),[])
(S,20,1,2014-08-12 09:27:16.4795874 UTC,2014-08-12 09:27:16.4795874 UTC,((\y # \y) + \x),[])
(S,19,1,2014-08-12 09:26:33.1259993 UTC,2014-08-12 09:26:33.1259993 UTC,((\z # \y) + (\x # \x)),[])
(S,13,6,2014-08-12 09:18:12.1432667 UTC,2014-08-12 09:24:56.1743315 UTC,((\x # \y) + \z),[((13,(3 # 0)),1),((13,(3 # 1)),1),((13,(4 # 2)),1),((14,(2 # 7)),1),((14,(3 # 0)),1),((14,(3 # 1)),1),((14,(4 # 2)),1),((15,(3 # 0)),1),((15,(3 # 1)),1),((15,(4 # 2)),1),((16,(3 # 0)),1),((16,(3 # 1)),1),((16,(4 # 2)),1)])
(S,11,3,2014-08-12 09:16:04.4344538 UTC,2014-08-12 09:23:09.6734973 UTC,((\z # \y) + \x),[((11,(6 # 8)),1),((12,(6 # 8)),2),((17,(6 # 8)),1),((18,(6 # 8)),1)])
(S,18,5,2014-08-12 09:20:28.2139021 UTC,2014-08-12 09:23:01.2274955 UTC,((\z # \x) + \y),[((8,(5 # 5)),3),((9,(5 # 5)),3),((11,(5 # 5)),2),((12,(5 # 5)),3),((12,(6 # 5)),2),((17,(5 # 5)),3),((17,(6 # 5)),2),((18,(5 # 5)),2)])
(S,17,4,2014-08-12 09:20:22.1445714 UTC,2014-08-12 09:22:42.9817767 UTC,(\z # (\x + \y)),[((8,(5 # 5)),2),((9,(5 # 5)),2),((12,(5 # 5)),2),((12,(6 # 5)),2),((17,(5 # 5)),2),((17,(6 # 5)),1)])
(S,16,2,2014-08-12 09:19:36.0471915 UTC,2014-08-12 09:19:38.2399705 UTC,((\x # \z) + \y),[((14,(2 # 9)),2),((15,(2 # 9)),2)])
(S,15,2,2014-08-12 09:19:27.4746955 UTC,2014-08-12 09:19:28.4470385 UTC,(\x # (\z + \y)),[((14,(2 # 9)),2),((15,(2 # 9)),1)])
(S,14,2,2014-08-12 09:18:21.0486503 UTC,2014-08-12 09:18:25.3471734 UTC,(\x # (\y + \z)),[((14,(2 # 7)),1)])
(S,12,2,2014-08-12 09:16:29.3925054 UTC,2014-08-12 09:16:32.8118917 UTC,(\z # (\y + \x)),[((12,(6 # 8)),1)])
(S,2,42,2014-08-10 12:09:28.3139811 UTC,2014-08-12 09:12:42.7432899 UTC,(\x + \y),[((1,1),2),((1,2),3),((2,1),1),((2,2),2),((2,5),1),((3,5),1)])
(S,8,19,2014-08-10 12:39:53.3778978 UTC,2014-08-12 09:10:56.9113566 UTC,(\y # (\x # \z)),[((8,(4 # 7)),5),((9,(4 # 7)),12),((9,(8 # 7)),2)])
(S,9,5,2014-08-10 12:41:08.9788049 UTC,2014-08-10 12:41:40.5766749 UTC,((\y + \x) # \z),[((9,(7 # 7)),1),((9,(8 # 7)),3)])
(S,7,9,2014-08-10 12:33:02.8660035 UTC,2014-08-10 12:36:38.7876249 UTC,(\x * \x),[((4,4),1)])
(S,6,32,2014-08-10 12:32:59.0815582 UTC,2014-08-10 12:36:35.5772525 UTC,(\y * \x),[((5,0),2),((5,2),1),((5,6),1),((5,8),1),((5,(1 # 0)),1),((5,(1 # 2)),2),((5,(1 # 4)),1),((5,(1 # 5)),1),((5,(1 # 6)),1),((5,(1 # 8)),2),((5,(2 # 0)),1),((5,(2 # 1)),1),((5,(2 # 4)),2),((5,(2 # 7)),1),((5,(2 # 8)),1),((5,(3 # 0)),1),((5,(3 # 2)),1),((5,(3 # 5)),1),((5,(3 # 6)),2),((5,(4 # 0)),1),((5,(4 # 2)),1),((5,(4 # 5)),1),((5,(4 # 8)),1),((5,(5 # 4)),1),((5,(5 # 6)),1),((5,(6 # 3)),1),((5,(7 # 2)),1),((6,(3 # 6)),1)])
(S,5,30,2014-08-10 12:28:42.3713066 UTC,2014-08-10 12:36:11.62544 UTC,(\x * \y),[])
(S,4,9,2014-08-10 12:23:59.3885936 UTC,2014-08-10 12:28:38.1234197 UTC,(\x + \x),[])
(S,3,39,2014-08-10 12:23:24.7410876 UTC,2014-08-10 12:28:35.5837737 UTC,(\y + \x),[((1,1),2),((1,2),1),((2,1),2),((2,2),1),((2,3),1),((2,4),1),((2,5),2),((2,6),2),((2,7),3),((2,8),3),((2,9),4),((2,(1 # 0)),4),((2,(1 # 1)),4),((2,(1 # 2)),3),((2,(1 # 3)),3),((2,(1 # 4)),2),((2,(1 # 5)),2),((2,(1 # 6)),1),((2,(1 # 7)),1),((3,1),1),((3,2),1),((3,3),1),((3,4),1),((3,5),2),((3,6),2),((3,7),3),((3,8),3),((3,9),4),((3,(1 # 0)),4),((3,(1 # 1)),4),((3,(1 # 2)),3),((3,(1 # 3)),3),((3,(1 # 4)),2),((3,(1 # 5)),2),((3,(1 # 6)),1),((3,(1 # 7)),1)])
