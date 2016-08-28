module TestData where
import Instances
import Parsing

-- "|" ,"&", "->", "<>"
logicTest :: [Item]
logicTest =
  map (\lhs -> Item "Logic" lhs (makeR "T") 1 Nothing)
   [(read "(P -> (((~ (~ P)) -> P) | Q))"), --  1. P -> ((~~P -> P) | Q)
    (read "(((~ P) <> P) -> (Q <> Q))"), --  2. (~P <> P) -> (Q <> Q)
    (read "((P | P) <> (~ (~ P)))"), --  3. (P | P) <> (~~P)
    (read "(((~ P) & P) -> Q)"), --  5. 
    (read "(P -> (Q -> P))"), --  7. 
    (read "(~ ((~ P) <> P))"), --  9. 
    (read "(((~ (P -> Q)) & R) -> (~ Q))"), -- 10. 
    (read "(~ (~ (~ (P & (~ P)))))"), -- 11. 
    (read "((P -> P) | Q)"), -- 12. 
    (read "((P & P) | (~ P))"), -- 15. 
    (read "(P | (P | (~ (Q & P))))"), -- 17. 
    (read "((P <> (~ P)) -> (Q <> P))"), -- 18. 
    (read "((~ ((P -> (~ Q)) | P)) -> Q)"), -- 21. 
    (read "(((P | (~ Q)) | Q) | P)"), -- 22. 
    (read "((P & P) -> P)"), -- 28. 
    (read "((P & P) <> P)"), -- 29. 
    (read "((~ (~ (P -> Q))) | (~ Q))"), -- 32. 
    (read "((P <> (Q <> (P | P))) -> Q)"), -- 33. 
    (read "((P <> P) | (P & (~ Q)))"), -- 35. 
    (read "((P & Q) -> (Q | R))"), -- 37. 
    (read "((~ P) -> (~ P))"), -- 40. 
    (read "(((~ P) | Q) | P)"), -- 42. 
    (read "((~ (P -> P)) -> Q)"), -- 43. 
    (read "(P <> (~ (~ P)))"), -- 44. 
    (read "(P -> ((P <> Q) | (Q -> R)))"), -- 45. 
    (read "((P -> Q) -> (P -> P))"), -- 50. 
    (read "((~ (P & P)) | (Q -> Q))"), -- 52. 
    (read "(P | (P -> (~ Q)))"), -- 56. 
    (read "(P | ((P -> Q) | P))"), -- 57. 
    (read "((P & ((Q -> P) <> P)) <> P)"), -- 62. 
    (read "(P | (Q | ((Q & R) <> P)))"), -- 63. 
    (read "(P | ((Q & Q) -> Q))"), -- 64. 
    (read "(P | (P -> Q))"), -- 66. 
    (read "(P -> (P | Q))"), -- 67. 
    (read "((~ (P -> Q)) | (Q -> Q))"), -- 69. 
    (read "(~ ((~ ((P -> Q) & Q)) & Q))"), -- 70. 
    (read "(P | (P -> (~ (~ (Q <> Q)))))"), -- 71. 
    (read "((P -> (~ Q)) | P)"), -- 72. 
    (read "((P -> (~ Q)) | Q)"), -- 76. 
    (read "((~ P) | (Q -> (P | P)))")  -- 77. 
   ]
