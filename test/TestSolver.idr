-- Copyright (c) 2013 Radek Micek

module TestSolver

import Solver

instance (Eq a, Eq b) => Eq (Either a b) where
  (Left x) == (Left y) = x == y
  (Right x) == (Right y) = x == y
  _ == _ = False

-- ---------------------------------------------------------------------------
-- Parser

test_parseLit_pos : so $ parseLit "c" == Right (MkLit Pos "c")
test_parseLit_pos = oh

test_parseLit_pos2 : so $ parseLit "Long_name" == Right (MkLit Pos "Long_name")
test_parseLit_pos2 = oh

test_parseLit_neg : so $ parseLit "!b" == Right (MkLit Neg "b")
test_parseLit_neg = oh

test_parseLit_neg2 : so $ parseLit "~X" == Right (MkLit Neg "X")
test_parseLit_neg2 = oh

test_parseLit_neg3 : so $ parseLit "~_" == Right (MkLit Neg "_")
test_parseLit_neg3 = oh

test_parseLit_empty : so $ isLeft $ parseLit ""
test_parseLit_empty = oh

test_parseLit_bad : so $ isLeft $ parseLit "~~a"
test_parseLit_bad = oh

test_parseLit_bad2 : so $ isLeft $ parseLit "1a"
test_parseLit_bad2 = oh

test_parseLits : so $ parseLits "a, ~a" == Right [MkLit Pos "a", MkLit Neg "a"]
test_parseLits = oh

test_parseLits2 : so $ parseLits "~lit | " == Right [MkLit Neg "lit"]
test_parseLits2 = oh

test_parseLits3 : so $ parseLits "a , ~b | c"
                         == Right [MkLit Pos "a", MkLit Neg "b", MkLit Pos "c"]
test_parseLits3 = oh

test_parseLits_bad : so $ isLeft $ parseLits "a | ~b | | ~c"
test_parseLits_bad = oh

-- ---------------------------------------------------------------------------
-- Solver

solveProb : SatAlgo Result () -> (Result, Assignment, List Event)
solveProb prob = solve' [] $ run emptySol (prob $> solve)
  where
    solve' : List i -> AlgoResult Sol i r -> (r, Assignment, List i)
    solve' is (Interrupt s i k) = solve' (i :: is) $ resume s k
    solve' is (Finish s r) = (r, trailToAssig $ sTrail s, is)

isSat : SatAlgo Result () -> List (List Lit) -> Bool
isSat prob lits = case solveProb prob of
  (Sat, assig, _) =>
    -- Some list of literals in lits is satisfied by assig.
    any (List.all $ \l => assig l == LTrue) lits
  _ => False

isUnsat : SatAlgo Result () -> Bool
isUnsat prob = case solveProb prob of
  (Unsat, _, _) => True
  _ => False

-- Satisfiable only by: a = 0, b = 0
--                      a = 0, b = 1
prob_sat : SatAlgo r ()
prob_sat = do
  addClause [MkLit Neg "a", MkLit Neg "b"]
  addClause [MkLit Neg "a", MkLit Pos "b"]
  return ()

test_solve_sat : so $ isSat prob_sat [ [MkLit Neg "a", MkLit Neg "b"]
                                     , [MkLit Neg "a", MkLit Pos "b"]
                                     ]
test_solve_sat = oh

-- Satisfiable only by: a = 0, b = 0
prob_sat2 : SatAlgo r ()
prob_sat2 = do
  addClause [MkLit Pos "a", MkLit Neg "b"]
  addClause [MkLit Neg "a", MkLit Neg "b"]
  addClause [MkLit Neg "a", MkLit Pos "b"]
  return ()

test_solve_sat2 : so $ isSat prob_sat2 [[MkLit Neg "a", MkLit Neg "b"]]
test_solve_sat2 = oh

prob_sat3 : SatAlgo r ()
prob_sat3 = return ()

test_solve_sat3 : so $ isSat prob_sat3 [[]]
test_solve_sat3 = oh

prob_unsat : SatAlgo r ()
prob_unsat = do
  addClause [MkLit Pos "a", MkLit Neg "b"]
  addClause [MkLit Neg "a", MkLit Neg "b"]
  addClause [MkLit Neg "a", MkLit Pos "b"]
  addClause [MkLit Pos "a", MkLit Pos "b"]
  return ()

test_solve_unsat : so $ isUnsat prob_unsat
test_solve_unsat = oh

prob_unsat2 : SatAlgo r ()
prob_unsat2 = do
  addClause []
  return ()

test_solve_unsat2 : so $ isUnsat prob_unsat2
test_solve_unsat2 = oh

mapM_ : Monad m => (a -> m b) -> List a -> m ()
mapM_ f = sequence_ . map f

php : Nat -> Nat -> SatAlgo r ()
php np nh = do
    -- Each pigeon is at least in one hole.
    mapM_ (\p => addClause $ map (ph Pos p) [1..nh]) [1..np]
    -- No hole contains two pigeons.
    let pigeonPairs = [(p, p2) | p <- [1..np], p2 <- [(p+1)..np]]
    mapM_
      (\h => mapM_ addClause
               $ map (\(p, p2) => [ph Neg p h, ph Neg p2 h]) pigeonPairs)
      [1..nh]
    -- No pigeon is in two holes.
    let holePairs = [(h, h2) | h <- [1..nh], h2 <- [(h+1)..nh]]
    mapM_
      (\p => mapM_ addClause
               $ map (\(h, h2) => [ph Neg p h, ph Neg p h2]) holePairs)
      [1..np]
  where
    ph : Sign -> Nat -> Nat -> Lit
    ph sign p h = MkLit sign $ "p" ++ show p ++ "h" ++ show h

test_solve_php32 : so $ isUnsat $ php 3 2
test_solve_php32 = oh

-- Needs massive amount of memory.
--test_solve_php43 : so $ isUnsat $ php 4 3
--test_solve_php43 = oh
