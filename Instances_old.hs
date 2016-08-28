-- Module Instances:  basic functions and instances
-- Author: Abdul Rahim Nizamani, ITIT, Gothenburg University, Sweden

module Instances where
import Prelude hiding (catch)
import Control.Exception (catch, IOException)
import System.IO
import Data.Time
import Data.List
import Data.Maybe (isJust,fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import System.Directory

class Size a where
    size :: a -> Int

data Exp = Var String | Root String | Unary String Exp | Binary String Exp Exp
           deriving (Eq,Ord)

data Item  = Item {lhs :: Lhs, rhs :: Rhs, val :: Int}
type Item' = (String,String,Int)

type Language = String
type Width = Int
type Depth = Int
type Comments = String
-- data Language = Boolean | List | Math | Logic | Stream | Analogy2 | Clause
--     deriving (Eq, Show)
-- type ConceptFile = FilePath
type IPFile = FilePath
type AgentMemory = ([Axiom],[Concept],[Shape])
data Agent = Agent Comments (Width, Depth, Int) AgentMemory

type ID    = Int
type Arity = Int
type Frequency = Int
type Rewarded = Int -- 0 for false, 1 for true. Indicates if a symbol appears in rhs
type FirstTime = UTCTime
type LastTime  = UTCTime

type Substitution = [(String,Exp)]

--type Concept' = (Arity,Rewarded,Frequency,FirstTime,LastTime,String)
newtype Concept  = C (Arity,Rewarded,Frequency,FirstTime,LastTime,Exp)

newtype Shape  = Shape (ID,Frequency,FirstTime,LastTime,Exp,[((ID,Rhs),Int)])

type WM =  Exp
type Lhs = Exp
type Rhs = Exp

data Axiom = Axiom {axLhs :: Lhs, axRhs :: Rhs, axV :: Int}

-------------------------------------------------------------------------------
---------------- INSTANCE DECLARATIONS ----------------------------------------
-------------------------------------------------------------------------------

instance Eq Axiom where
    (==) (Axiom x y _) (Axiom p q _) = x == p && y == q

instance Ord Axiom where
    compare (Axiom x y _) (Axiom p q _) | x == p = compare y q
    compare (Axiom x y _) (Axiom p q _) = compare x p

instance Size Item where
    size (Item x y _) = size x + size y

instance Size Exp where
    size (Var _) = 1
    size (Root _) = 1
    size (Unary a x) = size a + size x
    size (Binary a x y) = size a + size x + size y

instance Size Axiom where
    size (Axiom x y _) = size x + size  y

instance Size [a] where
    size xs = length xs

instance Size (Set a) where
    size x = Set.size x

instance Size (Map a b) where
    size x = Map.size x

instance Show Exp where
    show (Root a) = a
    show (Var "x") = "\\x"
    show (Var "y") = "\\y"
    show (Var "z") = "\\z"
    show (Var v) = "(\\v " ++ v ++ ")"
    show (Unary a e) = "(" ++ a ++ " " ++ show e ++ ")"
    show (Binary a e1 e2) = "(" ++ show e1 ++ " "  ++ a ++ " " ++ show e2 ++ ")"

instance Show Item where
    show (Item lhs rhs val) = "(" ++ show lhs ++ "," ++ show rhs ++ "," ++ show val ++ ")"

instance Show Axiom where
    show (Axiom x y v) = show x ++ " ==> " ++ show y ++ " : " ++ show v

instance Show Concept where
    show (C (arity,rew,freq,start,last,exp)) = 
        "(C," ++ show arity
            ++ "," ++ show rew
            ++ "," ++ show freq
            ++ "," ++ show start
            ++ "," ++ show last
            ++ "," ++ show exp
            ++ ")"

instance Show Shape where
    show (Shape (id,freq,start,last,exp,ids)) = 
        "(S," ++ show id
            ++ "," ++ show freq
            ++ "," ++ show start
            ++ "," ++ show last
            ++ "," ++ show exp
            ++ "," ++ show ids
            ++ ")"

isSolved = isGoal'

isGoal' :: Exp -> Bool
isGoal' (Root _) = True
isGoal' _ = False

isLeft (Left _) = True
isLeft _ = False
getLeft (Left r) = r

isRight (Right _) = True
isRight _ = False
getRight (Right r) = r

isInstanceOf :: Axiom -> Axiom -> Bool
isInstanceOf (Axiom f f' _) ax@(Axiom x x' _) = 
    let bind1 = expVarBinding x f
        bind2 = expVarBinding x' f'
    in if isJust bind1 && isJust bind2
        then let bind = fromJust bind1 ++ fromJust bind2
             in length bind == countVars ax && (null $ sameVarBinding bind)
        else False

instance' :: Exp -> Exp -> [(String,Exp)]
instance' = undefined

isPure ax = 
    let lhsvar = nub [v  |(Var v) <- getSubExp (axLhs ax)]
        rhsvar = nub [v  |(Var v) <- getSubExp (axRhs ax)]
    in null (rhsvar \\ lhsvar)

-- stability of constancts and variables: Every constant is unique
isStable ax = size (axLhs ax) > 1
              && axLhs ax /= axRhs ax
              && isPure ax

isFact :: Axiom -> Bool
isFact ax = not (containsVarAx ax) &&
            size (axLhs ax) <= 3 -- && size (axRhs ax) <= 3
            && not (axLhs ax == axRhs ax)

isAxiom :: Axiom -> Bool
isAxiom ax = notnull [v | (Var v) <- getSubExpAx ax]

isMixedPlus :: Axiom -> Bool
isMixedPlus ax =   notnull (nub [v | (Var v) <- subExp])
                && length (nub [c | (Root c) <- subExp]) == 1
                && ((sort $ nub [v | (Var v) <- lsub])
                     == (sort $ nub [v | (Var v) <- rsub]))
                -- && checkRhs t'
                && isStable ax
    where
        t      = axLhs ax
        t'     = axRhs ax
        lsub   = getSubExp t
        rsub   = getSubExp t'
        subExp = lsub ++ rsub

isMixed :: Axiom -> Bool
isMixed ax =   length (nub [v | (Var v) <- subExp]) == 1
            && length (nub [c | (Root c) <- subExp]) == 1
            && notnull [v | (Var v) <- lsub]
            && checkRhs t'
            && t /= t'
    where
        t      = axLhs ax
        t'     = axRhs ax
        lsub   = getSubExp t
        rsub   = getSubExp t'
        subExp = lsub ++ rsub
        checkRhs (Var _) = True
        checkRhs (Root _) = True
        checkRhs _ = False

isAlgebraic :: Axiom -> Bool
isAlgebraic ax = null [c | (Root c) <- (lhs' ++ rhs')] && 
                 ((sort $ nub [v | (Var v) <- lhs'])
                    == (sort $ nub [v | (Var v) <- rhs'])) && 
                 ((sort $ nub [u | (Unary u _) <- lhs'])
                    == (sort $ nub [u | (Unary u _) <- rhs'])) && 
                 ((sort $ nub [b | (Binary b _ _) <- lhs'])
                    == (sort $ nub [b | (Binary b _ _) <- rhs'])) &&
                 isStable ax
                 -- && size ax <= 7
    where
        lhs' = getSubExp (axLhs ax)
        rhs' = getSubExp (axRhs ax)

isAlgebraicAbs :: Axiom -> Bool
isAlgebraicAbs ax = null [c | (Root c) <- (lhs' ++ rhs')] && 
                   ((sort $ nub [v | (Var v) <- lhs'])
                      == (sort $ nub [v | (Var v) <- rhs'])) && 
                   -- ((sort $ nub [u | (Unary u _) <- lhs'])
                   --    == (sort $ nub [u | (Unary u _) <- rhs'])) && 
                   -- ((sort $ nub [b | (Binary b _ _) <- lhs'])
                   --    == (sort $ nub [b | (Binary b _ _) <- rhs'])) &&
                   isStable ax
                   -- && size ax <= 7
    where
        lhs' = getSubExp (axLhs ax)
        rhs' = getSubExp (axRhs ax)

isConservative :: Axiom -> Bool
isConservative ax = isAxiom ax && isStable ax
            && and [(Var v) `elem` lhs' | Var v <- rhs']
            && and [(Root c) `elem` lhs' | (Root c) <- rhs']
            && and [u `elem` [u' | (Unary u' _) <- lhs'] | (Unary u _) <- rhs']
            && and [b `elem` [b' | (Binary b' _ _) <- lhs'] | (Binary b _ _) <- rhs']
    where
        lhs' = getSubExp (axLhs ax)
        rhs' = getSubExp (axRhs ax)

expVarBinding :: Exp -> Exp -> Maybe [(String,Exp)]
expVarBinding (Var v) arg = Just [(v,arg)]
expVarBinding (Binary op1 p1 p2) (Binary op2 e1 e2) | op1 == op2 && isJust result1 && isJust result2
        = Just (fromJust result1 ++ fromJust result2)
           where
            result1 = expVarBinding p1 e1
            result2 = expVarBinding p2 e2
expVarBinding (Unary p p') (Unary e e') | p == e = expVarBinding p' e'
expVarBinding (Root x) (Root y) | x == y = Just []
expVarBinding _ _ = Nothing

containsVar :: Exp -> Bool
containsVar (Var _) = True
containsVar (Root _) = False
containsVar (Unary _ e) = containsVar e
containsVar (Binary _ e1 e2) = containsVar e1 || containsVar e2

containsVarAx :: Axiom -> Bool
containsVarAx (Axiom x y _) = containsVar x || containsVar y


countVarsUnique :: Axiom -> Int
countVarsUnique ax = length $ nub [v | Var v <- getSubExpAx ax]

countVars :: Axiom -> Int
countVars (Axiom p q _) = countVars' p + countVars' q
countVars' (Var _) = 1
countVars' (Root _) = 0
countVars' (Unary _ e) = countVars' e
countVars' (Binary _ e1 e2) = countVars' e1 + countVars' e2

countConsts :: Axiom -> Int
countConsts (Axiom p q _) = countConsts' p + countConsts' q

countConsts' (Var _) = 0
countConsts' (Root _) = 1
countConsts' (Unary _ e) = countConsts' e
countConsts' (Binary _ e1 e2) = countConsts' e1 + countConsts' e2

-- | Returns multiple bindings for the same variable, if any exist
sameVarBinding :: [(String,Exp)] -> [(String,Exp)]
sameVarBinding [] = []
--sameVarBinding :: [(HsQName,HsExp)] -> [(HsQName,HsExp)]
sameVarBinding ((name,exp):xs) =
    let xs'' = [(n,e) | (n,e) <- xs, n == name]
        xs'  = [(n,e) | (n,e) <- xs'', e /= exp]
    in if null xs'
            then sameVarBinding xs
            else ((name,exp):xs') ++ sameVarBinding [(n,e) | (n,e) <- xs, n /= name]

getSubExpAx :: Axiom -> [Exp]
getSubExpAx (Axiom x y _) = getSubExp x ++ getSubExp y

-- | returns a list of all subexpressions
getSubExp :: Exp -> [Exp]
getSubExp e = e : case e of
    (Unary _ x) -> getSubExp x
    (Binary _ x y) -> getSubExp x ++ getSubExp y
    _ -> []

-- | Replaces an Exp (exp) with an Exp (arg) in the main expression (rhs)
replaceExpInExp :: Rhs -> Exp -> Exp -> Exp
replaceExpInExp rhs (Var var) arg = replaceAllSubExp rhs var arg
replaceExpInExp rhs (Unary s1 e1) (Unary s2 e2) = replaceExpInExp rhs e1 e2
replaceExpInExp rhs (Binary s1 p1 p2) (Binary s2 e1 e2)
        = replaceExpInExp (replaceExpInExp rhs p1 e1) p2 e2
replaceExpInExp rhs _  _   = rhs

replaceAllSubExp :: Exp -> String -> Exp -> Exp
replaceAllSubExp exp v arg = case exp of
    Var v'  ->  v == v' ? arg $ exp
    Unary s e -> Unary s (replaceAllSubExp e v arg)
    Binary s e1 e2 -> Binary s (replaceAllSubExp e1 v arg) (replaceAllSubExp e2 v arg)
    _                  ->  exp

replaceAllSubExp2 :: Exp -> Exp -> Exp -> Exp
replaceAllSubExp2 exp v arg | exp == arg = v
replaceAllSubExp2 exp v arg = case exp of
    Var v'  ->  v == Var v' ? arg $ exp
    Unary s e -> Unary s (replaceAllSubExp2 e v arg)
    Binary s e1 e2 -> Binary s (replaceAllSubExp2 e1 v arg) (replaceAllSubExp2 e2 v arg)
    _                  ->  exp

notnull = not . null

wschars = " \t\r\n"
strip :: String -> String
strip = lstrip . rstrip
lstrip s = case s of
                  [] -> []
                  (x:xs) -> if elem x wschars
                            then lstrip xs
                            else s
rstrip = reverse . lstrip . reverse

-- Function to simulate if-then-else
if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

zipIf :: [Bool] -> [a] -> [a] -> [a]
zipIf = zipWith3 if'

infixr 1 ?
(?) :: Bool -> a -> a -> a
(?) = if'


readFileSafe :: FilePath ->  TextEncoding -> IO String
readFileSafe f enc = readFileSafe' f enc
     `catch`
        (\e -> do putStrLn ("Error in reading file " ++ f)
                  putStrLn $ "Exception: " ++ show (e :: IOException)
                  return "")


-- | Read file after checking its existence and permissions
readFileSafe' :: FilePath ->  TextEncoding -> IO String
readFileSafe' f enc = do
       e <- doesFileExist f
       if (not e)
         then do
           putStrLn $ "File " ++ f ++ " does not exist."
           return ""
         else do
           p <- getPermissions f
           if (not (readable p))
             then do
               putStrLn $ "Unable to read file " ++ f ++ "."
               return ""
             else do
               h <- openFile f ReadMode
               hSetEncoding h enc
               text <- hGetContents h
               putStrLn $ "Reading file " ++ show f ++ ", file length= " ++ show (length text)
               hClose h
               return text

