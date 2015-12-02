-- Copyright (c) 2015, Florian Mayer

-- Permission to use, copy, modify, and/or distribute this software for any
-- purpose with or without fee is hereby granted, provided that the above
-- copyright notice and this permission notice appear in all copies.

-- THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
-- WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
-- MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
-- ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
-- WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
-- ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
-- OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

import Data.List
import Data.Maybe

data Expr = Implication Expr Expr | Var String | Neg Expr deriving (Eq,Show)
data ExprSet = ExprSet [Expr] [Expr] [Expr] deriving (Eq,Show)
data Sequent = Sequent ExprSet ExprSet deriving (Eq,Show)

emptyExprSet = ExprSet [] [] []

getComposite :: ExprSet -> [Expr]
getComposite (ExprSet _ _ s) = s

getAtoms :: ExprSet -> [Expr]
getAtoms (ExprSet a _ _) = a

getNeg :: ExprSet -> [Expr]
getNeg (ExprSet _ n _) = n

isEmpty :: ExprSet -> Bool
isEmpty (ExprSet a b c) = (null a) && (null b) && (null c)

canAddLK :: ExprSet -> Bool
canAddLK _ = True

canAddLJ :: ExprSet -> Bool
canAddLJ = isEmpty

getAll :: ExprSet -> [Expr]
getAll (ExprSet a n s) = a ++ n ++ s

getLeftSide :: Sequent -> [Expr]
getLeftSide (Sequent (ExprSet a n s) rhs) | canAdd rhs = n ++ s
                                          | otherwise = s
addExpr :: ExprSet -> Expr -> ExprSet
addExpr (ExprSet as ns cs) a@(Var _) = ExprSet (a:as) ns cs
addExpr (ExprSet as ns cs) n@(Neg _) = ExprSet as (n:ns) cs
addExpr (ExprSet as ns cs) c = ExprSet as ns (c:cs)

removeExpr :: ExprSet -> Expr -> ExprSet
removeExpr (ExprSet as ns cs) e = (ExprSet (fn as) (fn ns) (fn cs))
                               where fn = delete e

isAxiom :: Sequent -> Bool
isAxiom (Sequent lhs rhs) = (not $ isEmpty rhs) && (any (\y -> any (== y) (getAll lhs)) $ getAll rhs) 

expandLeft :: Sequent -> Expr -> Maybe [Sequent]
expandLeft s@(Sequent lhs rhs) x@(Implication a b) = Just $ [Sequent nlhs (addExpr emptyExprSet a),
                                                             Sequent (addExpr nlhs b) rhs]
                                                  where nlhs = removeExpr lhs x
expandLeft s@(Sequent lhs rhs) x@(Neg a) | canAdd rhs = Just $ [Sequent (removeExpr lhs x) (addExpr rhs a)]
expandLeft _ _ = Nothing

expandRight :: Sequent -> Expr -> Maybe [Sequent]
expandRight s@(Sequent lhs rhs) x@(Implication a b) = Just $ [Sequent (addExpr lhs a) (addExpr (removeExpr rhs x) b)]
expandRight s@(Sequent lhs rhs) x@(Neg a) = Just $ [Sequent (addExpr lhs a) (removeExpr rhs x)]
expandRight _ _ = Nothing

stepLeft :: Sequent -> Maybe [Sequent]
stepLeft s = listToMaybe $ mapMaybe (expandLeft s) (getLeftSide s)

stepRight :: Sequent -> Maybe [Sequent]
stepRight s@(Sequent lhs rhs) = listToMaybe $ mapMaybe (expandRight s) ((getComposite rhs) ++ (getNeg rhs))

-- Apply stepLeft, if that returns Nothing, apply stepRight.
-- If both result in Nothing, return Nothing.
stepLK :: Sequent -> Maybe [Sequent]
stepLK s = listToMaybe $ catMaybes [stepLeft s, stepRight s]

-- Like normal step, just that when there is a value on the 
-- right side, but no more steps can be taken and the sequent
-- is not an axiom, drop the value on the right side and
-- try again.
stepLJ :: Sequent -> Maybe [Sequent]
stepLJ s@(Sequent lhs rhs) = case r of Just x -> Just x
                                       Nothing -> if (isAxiom s) || (isEmpty rhs) then Nothing
                                                  else Just $ [Sequent lhs emptyExprSet]
        where r = listToMaybe $ catMaybes [stepLeft s, stepRight s]

getFirst :: (Maybe a, a) -> a
getFirst ((Just x), _) = x
getFirst (_, y) = y  

-- Run step on all sequents. If step returns Nothing for all of then
-- also return nothing.
steps :: [Sequent] -> Maybe [Sequent]
steps xs = if all (isNothing . fst) nextIter then Nothing
                                             else Just $ concat $ map getFirst nextIter 
        where nextIter = map (\x -> (step x, [x])) xs

iterToNothing :: (a -> Maybe a) -> a -> a
iterToNothing fn x = case fn x of Nothing -> x
                                  Just y  -> iterToNothing fn y

step = stepLJ
canAdd = canAddLJ

-- Apply steps until it returns Nothing. That means that no more steps
-- need to be run. Then check whether all sequents are axioms.
solve :: Sequent -> Bool
solve s = all isAxiom $ iterToNothing steps [s]

toExprSet :: [Expr] -> ExprSet
toExprSet = foldl addExpr emptyExprSet
