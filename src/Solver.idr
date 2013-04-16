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

instance Ord Sign where
  compare Pos Pos = EQ
  compare Neg Neg = EQ
  compare Pos Neg = LT
  compare Neg Pos = GT

data Lit = MkLit Sign Var

instance Eq Lit where
  (MkLit sign var) == (MkLit sign' var') = sign == sign' && var == var'

instance Ord Lit where
  compare (MkLit s v) (MkLit s' v') =
    case compare s s' of
      LT => LT
      GT => GT
      EQ => compare v v'

instance Show Lit where
  show (MkLit Pos lit) = lit
  show (MkLit Neg lit) = strCons '~' lit

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

data Operation
  = OOther
  -- Current conflict clause, original conflict clause, processed variables.
  | OLearn (List Lit) Clause (List Var)
  | OMinimize (List Lit)
  -- Processed clauses, remaining clauses.
  | OPropagate (List Clause) (List Clause)

-- Solver state.
record Sol : Type where
  MkSol : (sClauses : List Clause) ->
          (sLevel : Level) ->
          (sTrail : Trail) ->
          (sOp : Operation) ->
          -- Corresponding clauses contain negations of the literals.
          (sWatched : List (CId, (Lit, Lit))) ->
          (sEnableMinimization : Bool) ->
          (sEnableWatchedLits : Bool) ->
          Sol

data Event
  = EDecide Lit
  | EProp Lit Clause
  | EConfl Clause
  | EWShortClause Lit Clause
  | EWPropLitStart Lit
  -- Watched literal which is being propagated,
  -- other watched literal which is true, clause.
  | EWOtherLitTrue Lit Lit Clause
  -- Watched literal which is being propagated,
  -- not watched literal which is not false, clause.
  | EWReplaceLit Lit Lit Clause
  -- Watched literal which is being propagated,
  -- other watched literal which is false, clause.
  | EWConfl Lit Lit Clause
  -- Watched literal which is being propagated,
  -- other watched literal which is unassigned, clause.
  | EWProp Lit Lit Clause
  | EAnalyzeStart Clause
  -- Variable to be resolved on, current conflict clause,
  -- antecedent clause of the variable, resolvent.
  | EResolve Var (List Lit) Clause (List Lit)
  | ESkip Var (List Lit) Clause
  | EAnalyzeEnd (List Lit)
  -- Candidates for removal, asserting clause.
  | EMinStart (List Lit) (List Lit)
  | ETestRedundant Lit (List Lit)
  | ERedundant Lit (List Lit)
  | ENotRedundant Lit (List Lit)
  -- Redundant literals, original asserting clause,
  -- minimized asserting clause.
  | EMinEnd (List Lit) (List Lit) (List Lit)
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
emptySol = MkSol [] 0 [] OOther [] True True

negLit : Lit -> Lit
negLit (MkLit Pos l) = MkLit Neg l
negLit (MkLit Neg l) = MkLit Pos l

getLits : Clause -> List Lit
getLits (MkClause _ lits) = lits

findInTrail : Var -> Trail -> Maybe (Lit, Maybe Ante, Level)
findInTrail var = find (\(MkLit _ v, _, _) => v == var)

findClause : CId -> List Clause -> Clause
findClause cid = fromJust . find (\(MkClause cid' _) => cid == cid')

trailToAssig : Trail -> Assignment
trailToAssig trail l =
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

findClauseToProp : Assignment -> List Clause -> Maybe (Clause, Prop)
findClauseToProp _ [] = Nothing
findClauseToProp assig (c::cs) =
  case testClause assig c of
    Just p => Just (c, p)
    Nothing => findClauseToProp assig cs

-- Unit propagation. Returns conflict clause.
propagate : SatAlgo r (Maybe Clause)
propagate = do
  s <- get
  let assig = trailToAssig $ sTrail s
  let clauses = sClauses s
  let clause = findClauseToProp assig clauses
  case clause of
    Just (cl, Unit l) => do
      let MkClause cid _ = cl
      assign l $ Just cid
      interrupt $ EProp l cl
      propagate
    Just (cl, Conflict) => return $ Just cl
    Nothing => return Nothing

wpropagate : SatAlgo r (Maybe Clause)
wpropagate = do
    confl <- propagateShort
    case confl of
      Just _ => return confl
      _ => firstLit >>= propagateWatched
  where
    findShortToProp : Assignment -> List Clause -> Maybe (Clause, Prop)
    findShortToProp _ [] = Nothing
    findShortToProp _ (MkClause cid [] :: _) =
      Just (MkClause cid [], Conflict)
    findShortToProp assig (MkClause cid [l] :: cs) =
      case assig l of
        LTrue => findShortToProp assig cs
        LFalse => Just (MkClause cid [l], Conflict)
        LUndef => Just (MkClause cid [l], Unit l)
    findShortToProp assig (_ :: cs) = findShortToProp assig cs

    propagateShort : SatAlgo r (Maybe Clause)
    propagateShort = do
      s <- get
      if sLevel s == 0 then
        case findShortToProp (trailToAssig $ sTrail s) (sClauses s) of
          Nothing => return Nothing
          -- There should be no empty clause.
          Just (cl, Conflict) => return $ Just cl
          Just (MkClause cid lits, Unit l) => do
            assign l $ Just cid
            interrupt $ EWShortClause l $ MkClause cid lits
            propagateShort
      else
        return Nothing

    -- The first literal in the propagation queue.
    firstLit : SatAlgo r (Maybe Lit)
    firstLit = do
      s <- get
      case dropWhile (\(_, _, lvl) => lvl /= sLevel s) $ reverse (sTrail s) of
        [] => return $ Nothing
        (l, _, _) :: _ => return $ Just l

    -- Next literal in the propagation queue.
    nextLit : Lit -> SatAlgo r (Maybe Lit)
    nextLit lit = do
      s <- get
      case dropWhile (\(l, _, _) => l /= lit) $ reverse (sTrail s) of
        _ :: (l, _, _) :: _ => return $ Just l
        _ => return Nothing

    propagateWatched : Maybe Lit -> SatAlgo r (Maybe Clause)
    -- Propagation queue is empty.
    propagateWatched Nothing = return Nothing
    propagateWatched (Just lit) = do
        s <- get

        -- Find clauses where lit is watched.
        let clauses : List Clause =
          map (\(cid, _) => findClause cid $ sClauses s)
            $ filter (\(cid, (l, l')) => l == lit || l' == lit)
            $ sWatched s

        putOp [] clauses

        interrupt $ EWPropLitStart (negLit lit)

        confl <- propClauses [] clauses
        case confl of
          Nothing => nextLit lit >>= propagateWatched
          confl => return confl
      where
        putOp : List Clause -> List Clause -> SatAlgo r ()
        putOp proc remaining = do
          s <- get
          case remaining of
            [] => put (record { sOp = OOther } s)
            _ :: _ => put (record { sOp = OPropagate proc remaining } s)
        propClauses : List Clause -> List Clause -> SatAlgo r (Maybe Clause)
        propClauses proc [] = return Nothing
        propClauses proc (c :: cs) = do
          putOp (c :: proc) cs
          s <- get

          let (MkClause cid lits) = c
          let (_, (wl, wl')) = fromJust
                                 $ List.find (\(cid', _) => cid == cid')
                                 $ sWatched s
          let lit' = (wl == lit) ? wl' : wl
          let assig = trailToAssig $ sTrail s

          case assig $ negLit lit' of
            LTrue => do
              interrupt $ EWOtherLitTrue (negLit lit) (negLit lit') c
              propClauses (c :: proc) cs
            a =>
              -- Find replacement for lit.
              case
                find (\l => negLit l /= lit &&
                            negLit l /= lit' &&
                            assig l /= LFalse)
                     lits
              of
                Just newLit => do
                  -- Replace watched literal.
                  s2 <- get
                  let (ws, ws') = List.break (\(cid', _) => cid == cid')
                                    $ sWatched s2
                  let watched : List (CId, (Lit, Lit)) =
                    ws ++ ((cid, (negLit newLit, lit')) :: tl ws')
                  put (record { sWatched = watched } s2)

                  interrupt $ EWReplaceLit (negLit lit) newLit c
                  propClauses (c :: proc) cs
                Nothing =>
                  if a == LFalse then do
                    putOp (c :: proc) []
                    interrupt $ EWConfl (negLit lit) (negLit lit') c
                    return $ Just c
                  else do
                    assign (negLit lit') $ Just cid
                    interrupt $ EWProp (negLit lit) (negLit lit') c
                    propClauses (c :: proc) cs

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

addClause' : List Lit -> Maybe (Lit, Lit) -> SatAlgo r Clause
addClause' lits watch = do
  s <- get
  let clauses = sClauses s
  let cid = MkCId $ length clauses + 1
  let cl = MkClause cid lits
  let watched =
    if sEnableWatchedLits s then
      case watch of
        Just (l, l') => sWatched s ++ [(cid, (negLit l, negLit l'))]
        Nothing =>
          case lits of
            l :: l' :: _ => sWatched s ++ [(cid, (negLit l, negLit l'))]
            _ => sWatched s
    else
      sWatched s
  put (record { sClauses = clauses ++ [cl], sWatched = watched } s)
  return cl

addClause : List Lit -> SatAlgo r Clause
addClause lits = addClause' lits Nothing

-- Literal must be assigned.
litToLevel : Trail -> Lit -> Level
litToLevel trail (MkLit _ v) = level $ fromJust $ findInTrail v trail
  where
    level (_, _, l) = l

litRedundant : List Lit -> Lit -> SatAlgo r Bool
litRedundant assertingCl = \l => get >>= litRedundant' (negLit l)
  where
    -- Literal must be in the trail (i.e. it must be true).
    litRedundant' : Lit -> Sol -> SatAlgo r Bool
    litRedundant' literal s = do
        let (MkLit _ variable) = literal
        let (_, antecedent, _) = fromJust $ findInTrail variable $ sTrail s
        let anteLits = getLits $ findClause (fromJust antecedent) $ sClauses s
        let queue = List.map negLit $ filter (/= literal) anteLits
        let (b, highlight) = bfs queue $ map (\l => (l, Nothing)) queue

        put (record { sOp = OMinimize highlight } s)
        interrupt $ ETestRedundant (negLit literal) assertingCl

        put (record { sOp = OOther } s)
        if b then
          interrupt $ ERedundant (negLit literal) assertingCl
        else
          interrupt $ ENotRedundant (negLit literal) assertingCl

        return b
      where
        Redundant : Type
        Redundant = Bool
        Marked : Type
        Marked = (Lit, Maybe Lit)
        bfs : List Lit -> List Marked -> (Redundant, List Lit)
        bfs [] marked = (True, map fst marked) -- Literal is redundant.
        bfs (q :: qs) marked =
          -- Literal ~q is in asserting clause.
          if negLit q `elem` assertingCl then
            bfs qs marked
          else
            let (MkLit _ var) = q in
            case fromJust $ findInTrail var (sTrail s) of
              -- Literal isn't redundant.
              (_, Nothing, _) => (False, constructPath q)
              (_, Just _, O) => bfs qs marked
              (_, Just cid, _) =>
                let newLits : List Lit =
                  filter (\l => all ((/= l) . fst) marked) -- l is not marked.
                    $ map negLit
                    $ filter (/= q)
                    $ getLits
                    $ findClause cid (sClauses s) in
                -- Add antecedents to the queue and mark them.
                bfs
                  (qs ++ newLits)
                  (marked ++ map (\l => (l, Just q)) newLits)
          where
            constructPath : Lit -> List Lit
            constructPath lit =
              case fromJust $ find (\(l, _) => l == lit) marked of
                (_, Nothing) => [lit]
                (_, Just l) => lit :: constructPath l

-- Common.filterM doesn't work for some reason.
filterM' : (a -> SatAlgo r Bool) -> List a -> SatAlgo r (List a)
filterM' _ [] = return List.Nil
filterM' p (x :: xs) = do
  b <- p x
  ys <- filterM' p xs
  return (b ? List.(::) x ys : ys)

minimize : List Lit -> SatAlgo r (List Lit)
minimize assertingCl = do
    s <- get

    let candidates : List Lit =
      map (negLit . getLit)
        -- Skip decided literals.
        $ filter (\(_, ante, _) => isJust ante)
        -- Skip literal from current decision level.
        $ filter (\(_, _, lvl) => sLevel s /= lvl)
        $ List.map fromJust
        $ List.map (\(MkLit _ var) => findInTrail var $ sTrail s) assertingCl

    interrupt $ EMinStart candidates assertingCl

    redundant <- filterM' (litRedundant assertingCl) candidates
    let newAssertingCl = filter (\l => List.all (/= l) redundant) assertingCl

    interrupt $ EMinEnd redundant assertingCl newAssertingCl

    return newAssertingCl
  where
    getLit : (Lit, Maybe Ante, Level) -> Lit
    getLit (l, _, _) = l

isAsserting : List Lit -> Level -> Trail -> Bool
isAsserting lits level trail = (List.length $ filter (== level) levels) == 1
  where
      levels : List Nat
      levels = map (litToLevel trail) $ nub lits

-- Returns a learned clause.
-- If decision level > 0 then the learned clause is nonempty.
analyzeConflict : Clause -> SatAlgo r (List Lit)
analyzeConflict conflClause = do
    let conflLits = getLits conflClause
    s <- get
    put (record { sOp = OLearn conflLits conflClause [] } s)
    interrupt $ EAnalyzeStart conflClause
    assertingLits <- resolve s (sTrail s) conflLits []
    put (record { sOp = OOther } s)
    interrupt $ EAnalyzeEnd assertingLits
    return assertingLits
  where
    partial
    resolve : Sol -> Trail -> List Lit -> List Var -> SatAlgo r (List Lit)
    resolve s trail lits procVars =
      if isAsserting lits (sLevel s) (sTrail s) then
        return lits
      else
        case trail of
          (MkLit _ var, Just ante, _) :: ts => do
            let procVars' = var :: procVars
            let anteCl = findClause ante $ sClauses s
            if find (\(MkLit _ v) => v == var) lits == Nothing then do
              put (record { sOp = OLearn lits conflClause procVars' } s)
              interrupt $ ESkip var lits anteCl
              resolve s ts lits procVars'
            -- var is among lits, so we resolve it out.
            else do
              let anteLits = getLits anteCl
              let resolvent =
                List.nub
                  $ filter (\(MkLit _ v) => v /= var)
                  $ lits ++ anteLits
              put (record { sOp = OLearn resolvent conflClause procVars' } s)
              interrupt $ EResolve var lits anteCl resolvent
              resolve s ts resolvent procVars'
          -- missing case: []

-- Assumes that every literal in the clause is assigned.
computeBacktrackLevel : List Lit -> Trail -> (Level, Maybe (Lit, Lit))
computeBacktrackLevel lits trail =
  case groupBy sameLevel $ reverse $ sort lits' of
    ((_, l) :: _) :: ((lvl, l') :: _) :: _ => (lvl, Just (l, l'))
    _ => (0, Nothing)
  where
    lits' : List (Level, Lit)
    lits' = map (\l => (litToLevel trail l, l)) lits
    sameLevel : (Level, Lit) -> (Level, Lit) -> Bool
    sameLevel (l, _) (l2, _) = l == l2

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
  conflCl <- get >>= (\s => (sEnableWatchedLits s) ? wpropagate : propagate)
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
        assertingCl <- analyzeConflict confl
        assertingCl' <-
          (sEnableMinimization s) ? minimize assertingCl : return assertingCl
        let (blevel, watch) = computeBacktrackLevel assertingCl' (sTrail s)
        learned <- addClause' assertingCl' watch
        interrupt (ELearn learned)
        backtrack blevel
        solve

-- ---------------------------------------------------------------------------
-- Parser

whitespace : Char -> Bool
whitespace c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

asciiIdent : String -> Bool
asciiIdent s with (unpack s)
  asciiIdent _ | [] = False
  asciiIdent _ | (x :: xs) = asciiAlphaUsc x && all asciiAlphaNumUsc xs
  where
    asciiAlphaUsc : Char -> Bool
    asciiAlphaUsc c =
      (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_'
    asciiAlphaNumUsc : Char -> Bool
    asciiAlphaNumUsc c = asciiAlphaUsc c || (c >= '0' && c <= '9')

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
    str' = filter (not . whitespace) str
    lit : Lit
    lit =
      case str' of
        '~' :: var => MkLit Neg (pack var)
        '!' :: var => MkLit Neg (pack var)
        var => MkLit Pos (pack var)

-- Tolerates literal separator after the last literal.
parseLits' : List Char -> Either String (List Lit)
parseLits' str =
  if all whitespace str then
    Right []
  else
    let (litStr, restStr) = break litSep str in
    case (parseLit' litStr, parseLits' $ drop 1 restStr) of
      (Left err, _) => Left err
      (_, Left err) => Left err
      (Right l, Right ls) => Right $ l :: ls
  where
    litSep : Char -> Bool
    litSep c = c == ',' || c == '|' || c == ';'

parseLit : String -> Either String Lit
parseLit = parseLit' . unpack

parseLits : String -> Either String (List Lit)
parseLits = parseLits' . unpack
