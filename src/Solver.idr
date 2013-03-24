-- Copyright (c) 2013 Radek Micek

module Solver

import Algo

partial
hd : List a -> a
hd (x :: _) = x
-- missing case: hd []

partial
tl : List a -> List a
tl (_ :: xs) = xs
-- missing case: tl []

partial
fromJust : Maybe a -> a
fromJust (Just x) = x
-- missing case: fromJust Nothing

groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy _ [] = []
groupBy eq (x :: xs) =
  let (ys, zs) = span (eq x) xs in
  (x :: ys) :: groupBy eq zs

Var : Type
Var = String

data Sign = Pos | Neg

instance Eq Sign where
  Pos == Pos = True
  Neg == Neg = True
  _ == _ = False

data Lit = MkLit Sign Var

instance Eq Lit where
  (MkLit sign var) == (MkLit sign' var') = sign == sign' && var == var'

instance Show Lit where
  show (MkLit Pos lit) = lit
  show (MkLit Neg lit) = strCons '~' lit

-- Fay does not support newtype.
data CId = MkCId Nat

instance Eq CId where
  (MkCId x) == (MkCId y) = x == y

-- Must not contain any duplicate literals.
data Clause = MkClause CId (List Lit)

-- Decision level.
Level : Type
Level = Nat

Ante : Type
Ante = CId

Trail : Type
Trail = List (Lit, Maybe Ante, Level)

-- Solver state.
record Sol : Type where
  MkSol : (sClauses : List Clause) ->
          (sLevel : Level) ->
          (sTrail : Trail) ->
          Sol

data Event
  = EDecide Lit
  | EProp Lit Clause
  | EConfl Clause
  | ELearn Clause
  | EBacktrack Lit (Maybe Clause)

SatAlgo : Type -> Type -> Type
SatAlgo = Algo Sol Event

data LBool = LTrue | LFalse | LUndef

instance Eq LBool where
  LTrue == LTrue = True
  LFalse == LFalse = True
  LUndef == LUndef = True
  _ == _ = False


Assignment : Type
Assignment = Lit -> LBool

emptySol : Sol
emptySol = MkSol [] 0 []

getLits : Clause -> List Lit
getLits (MkClause _ lits) = lits

findInTrail : Var -> Trail -> Maybe (Lit, Maybe Ante, Level)
findInTrail var = find (\(MkLit _ v, _, _) => v == var)

findClause : CId -> List Clause -> Clause
findClause cid = fromJust . find (\(MkClause cid' _) => cid == cid')

trailToAssig : Trail -> Assignment
trailToAssig trail = \l =>
  let (MkLit _ var) = l in
  case findInTrail var trail of
    Nothing => LUndef
    Just (l', _, _) => if l == l' then LTrue else LFalse

data Prop = Unit Lit | Conflict

testClause : Assignment -> Clause -> Maybe Prop
testClause assig (MkClause _ lits) =
  if sat then
    Nothing
  else
    -- Note: nub is redundant when clause has no duplicate literals.
    case List.nub $ filter ((== LUndef) . assig) lits of
      [] => Just Conflict
      [l] => Just $ Unit l
      _ => Nothing
  where
    sat = not $ isNil $ filter ((== LTrue) . assig) lits

-- Manages decision level.
assign : Lit -> Maybe Ante -> SatAlgo r ()
assign l ante = do
  s <- get
  let trail = sTrail s
  let lvl : Nat =
    case ante of
      Nothing => sLevel s + 1
      Just _ => sLevel s
  put (record { sTrail = (l, ante, lvl) :: trail, sLevel = lvl } s)

findClauseToProp : Assignment -> List Clause -> SatAlgo r (Maybe (Clause, Prop))
findClauseToProp _ [] = return Nothing
findClauseToProp assig (c::cs) =
  case testClause assig c of
    Just p => return $ Just (c, p)
    Nothing => findClauseToProp assig cs

-- Unit propagation. Returns conflict clause.
propagate : SatAlgo r (Maybe Clause)
propagate = do
  s <- get
  let assig = trailToAssig $ sTrail s
  let clauses = sClauses s
  clause <- findClauseToProp assig clauses
  case clause of
    Just (cl, Unit l) => do
      let MkClause cid _ = cl
      assign l $ Just cid
      interrupt $ EProp l cl
      propagate
    Just (cl, Conflict) => return $ Just cl
    Nothing => return Nothing

unassignedVars : Assignment -> List Clause -> List Var
unassignedVars assig clauses =
  filter ((== LUndef) . assig . MkLit Pos) vars
  where
    varsInClause : Clause -> List Var
    varsInClause (MkClause _ lits) = nub $ map (\(MkLit _ var) => var) lits
    vars : List Var
    vars = nub $ concatMap varsInClause clauses

choose : SatAlgo r (Maybe Lit)
choose = do
  -- TODO: let user choose
  s <- get
  let vars = unassignedVars (trailToAssig $ sTrail s) (sClauses s)
  case vars of
    [] => return Nothing
    v::_ => return $ Just $ MkLit Pos v

addClause : List Lit -> SatAlgo r Clause
addClause lits = do
  s <- get
  let clauses = sClauses s
  let cl = MkClause (MkCId $ length clauses + 1) lits
  put (record { sClauses = clauses ++ [cl] } s)
  return cl

-- Literal must be assigned.
litToLevel : Trail -> Lit -> Level
litToLevel trail (MkLit _ v) = level $ fromJust $ findInTrail v trail
  where
    level (_, _, l) = l

isAsserting : List Lit -> Level -> Trail -> Bool
isAsserting lits level trail = (List.length $ filter (== level) levels) == 1
  where
      levels : List Nat
      levels = map (litToLevel trail) $ nub lits

-- Returns a learned clause.
-- If decision level > 0 then the learned clause is nonempty.
analyzeConflict : Clause -> SatAlgo r Clause
analyzeConflict (MkClause _ conflLits) = do
    s <- get
    assertingLits <- resolve s (sTrail s) conflLits
    addClause assertingLits
  where
    partial
    resolve : Sol -> Trail -> List Lit -> SatAlgo r (List Lit)
    resolve s trail lits =
      if isAsserting lits (sLevel s) (sTrail s) then
        return lits
      else
        case trail of
          (MkLit _ var, Just ante, _) :: ts => do
            let anteCl =
              fromJust
                $ List.find (\(MkClause cid _) => cid == ante)
                $ sClauses s
            let anteLits = getLits anteCl
            let resolvent =
              List.nub
                $ filter (\(MkLit _ v) => v /= var)
                $ lits ++ anteLits
            resolve s ts resolvent
          -- missing case: []

-- Assumes that every literal in the clause is assigned.
computeBacktrackLevel : Clause -> Trail -> Level
computeBacktrackLevel (MkClause _ lits) trail =
  hd $ hd $ tl $ (groupBy (==) $ reverse $ sort levels) ++ [[0]]
  where
    levels = map (litToLevel trail) lits

backtrack : Level -> SatAlgo r ()
backtrack level = do
  s <- get
  let trail = sTrail s
  case trail of
    (lit, ante, l) :: ts =>
      if l > level then do
        put (record { sTrail = ts } s)
        let cl = [| findClause ante (pure $ sClauses s) |]
        interrupt (EBacktrack lit cl)
        backtrack level
      else
        put $ record { sLevel = level } s
    [] =>
      put $ record { sLevel = level } s

data Result = Sat | Unsat

instance Eq Result where
  Sat == Sat = True
  Unsat == Unsat = True
  _ == _ = False

instance Show Result where
  show Sat = "Sat"
  show Unsat = "Unsat"

solve : SatAlgo r Result
solve = do
  conflCl <- propagate
  case conflCl of
    Nothing => do
      lit <- choose
      case lit of
        -- All variables are assigned.
        Nothing => return Sat
        Just l => do
          assign l Nothing
          interrupt (EDecide l)
          solve
    Just confl => do
      interrupt (EConfl confl)
      s <- get
      if sLevel s == 0 then
        return Unsat
      else do
        learned <- analyzeConflict confl
        interrupt (ELearn learned)
        let blevel = computeBacktrackLevel learned (sTrail s)
        backtrack blevel
        solve

-- ---------------------------------------------------------------------------
-- Parser

asciiAlpha : List Char
asciiAlpha = map chr $ [ord 'A' .. ord 'Z'] ++ [ord 'a' .. ord 'z']
  where
    chr = prim__intToChar
    ord = prim__charToInt

asciiAlphaNum : List Char
asciiAlphaNum = map chr [ord '0' .. ord '9'] ++ asciiAlpha
  where
    chr = prim__intToChar
    ord = prim__charToInt

whitespace : List Char
whitespace = unpack " \t\n\r"

asciiIdent : String -> Bool
asciiIdent s with (unpack s)
  asciiIdent _ | [] = False
  asciiIdent _ | (x :: xs) =
    (x `elem` ('_' :: asciiAlpha)) &&
    (all (flip List.elem ('_' :: asciiAlphaNum)) xs)

parseLit' : List Char -> Either String Lit
parseLit' str =
  case lit of
    MkLit _ v =>
      if not $ asciiIdent v then
        Left $ "Invalid identifier: '" ++ v ++ "'"
      else
        Right lit
  where
    str' : List Char
    str' = filter (not . flip List.elem whitespace) str
    lit : Lit
    lit =
      case str' of
        '~' :: var => MkLit Neg (pack var)
        '!' :: var => MkLit Neg (pack var)
        var => MkLit Pos (pack var)

-- Tolerates literal separator after the last literal.
parseLits' : List Char -> Either String (List Lit)
parseLits' str =
  if all (flip List.elem whitespace) str then
    Right []
  else
    let litSep = flip List.elem $ unpack ",|;" in
    let (litStr, restStr) = break litSep str in
    case (parseLit' litStr, parseLits' $ drop 1 restStr) of
      (Left err, _) => Left err
      (_, Left err) => Left err
      (Right l, Right ls) => Right $ l :: ls

parseLit : String -> Either String Lit
parseLit = parseLit' . unpack

parseLits : String -> Either String (List Lit)
parseLits = parseLits' . unpack