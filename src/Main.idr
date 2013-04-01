-- Copyright (c) 2013 Radek Micek

module Main

import Common
import D3
import Solver

-- ---------------------------------------------------------------------------
-- References

data IORef a = MkIORef (Array a)

newIORef : a -> IO (IORef a)
newIORef x = pure MkIORef <$> mkArray [x]

readIORef : IORef a -> IO a
readIORef (MkIORef arr) = getNth arr 0

writeIORef : IORef a -> a -> IO ()
writeIORef (MkIORef arr) x = setNth arr 0 x

modifyIORef : IORef a -> (a -> a) -> IO ()
modifyIORef r f = (pure f <$> readIORef r) >>= writeIORef r

-- ---------------------------------------------------------------------------

litToHtml : Lit -> String
litToHtml (MkLit Pos lit) = lit
litToHtml (MkLit Neg lit) = "&#172;" ++ lit

clauseToHtml : Clause -> String
clauseToHtml (MkClause _ lits) =
  case lits of
    [] => "&#9633;"
    l :: ls =>
      litToHtml l ++ mconcat (map (\l' => " &#8744; " ++ litToHtml l') ls)

-- ---------------------------------------------------------------------------
-- Message view

data MsgView = MkMsgView (Sel NoData NoData)

createMsgView : String -> Sel a b -> IO MsgView
createMsgView cssClass parent = do
  pure MkMsgView <$> (parent ??
    append "div" >=>
    forgetBoundData >=>
    classed cssClass True)

refreshMsgView : MsgView -> String -> IO ()
refreshMsgView (MkMsgView v) msg = do
  v ?? text msg
  return ()

refreshMsgViewHtml : MsgView -> String -> IO ()
refreshMsgViewHtml (MkMsgView v) msg = do
  v ?? html msg
  return ()

-- ---------------------------------------------------------------------------
-- Clause view

data ClauseView = MkClauseView (Sel NoData NoData)

createClauseView : String -> Sel a b -> IO ClauseView
createClauseView cssClass parent = do
  pure MkClauseView <$> (parent ??
    append "ul" >=>
    forgetBoundData >=>
    classed cssClass True >=>
    classed "clauseViewRoot" True)

refreshClauseView : ClauseView -> List Clause -> Trail -> IO ()
refreshClauseView (MkClauseView v) clauseList trail = do
    clauseArr <- emptyA ()
    mapM_ (mkArray . getLits >=> pushA clauseArr) clauseList

    let assig = trailToAssig trail

    clauses <- v ?? selectAll "ul.clauseViewRoot > li" >=>
               bind clauseArr
    clauses ?? exit >=> remove
    clauses ?? enter >=>
      append "li" >=>
      append "ul"

    lits <- clauses ?? select "ul" >=>
              selectAll "li" >=>
              bind' (\d, i => return d)
    lits ?? exit >=> remove
    lits ?? enter >=>
      append "li"

    lits ??
      html' (\lit, i => return $ litToHtml lit) >=>
      attr' "class" (\lit, i => return $ litClass $ assig lit)

    return ()
  where
    litClass : LBool -> String
    litClass LTrue = "sat"
    litClass LFalse = "unsat"
    litClass LUndef = "unassigned"

-- ---------------------------------------------------------------------------
-- Assignment view

data AssigView = MkAssigView (Sel NoData NoData)

createAssigView : String -> Sel a b -> IO AssigView
createAssigView cssClass parent = do
  pure MkAssigView <$> (parent ??
    append "ul" >=>
    forgetBoundData >=>
    classed cssClass True >=>
    classed "assigViewRoot" True)

refreshAssigView : AssigView -> List Clause -> Trail -> IO ()
refreshAssigView (MkAssigView v) clauses trail = do
    trailArr <- emptyA ()
    mapM_ (mkArray >=> pushA trailArr) $ groupBy sameLevel $ reverse trail

    levels <- v ?? selectAll "ul.assigViewRoot > li" >=>
                bind trailArr
    levels ?? exit >=> remove
    levels ?? enter >=>
      append "li" >=>
      append "ul"

    lits <- levels ?? select "ul" >=>
              selectAll "li" >=>
              bind' (const . pure)
    lits ?? exit >=> remove
    lits ?? enter >=>
      append "li"

    lits ??
      html' (const . pure . litHtml) >=>
      attr' "title" (const . decodeEntities . litTitle) >=>
      attr' "class" (const . pure . litClass)

    return ()
  where
    sameLevel : (Lit, Maybe Ante, Level) -> (Lit, Maybe Ante, Level) -> Bool
    sameLevel (_, _, l) (_, _, l') = l == l'
    litTitle : (Lit, Maybe Ante, Level) -> String
    litTitle (_, Nothing, _) = ""
    litTitle (_, Just cid, _) = clauseToHtml $ findClause cid clauses
    litHtml : (Lit, Maybe Ante, Level) -> String
    litHtml (lit, _, _) = litToHtml lit
    litClass : (Lit, Maybe Ante, Level) -> String
    litClass (_, Nothing, _) = "decided"
    litClass (_, Just _, _) = "forced"

-- ---------------------------------------------------------------------------

record State : Type where
  MkState :
    (stSol : Sol) ->
    (stLastInterrupt : Maybe (Event, Sol -> AlgoResult Sol Event Result)) ->
    (stMsgView : MsgView) ->
    (stClauseView : ClauseView) ->
    (stAssigView : AssigView) ->
    (stAddClauseBtn : Sel NoData NoData) ->
    (stStartVisBtn : Sel NoData NoData) ->
    (stNextBtn : Sel NoData NoData) ->
    State

-- Updates the message and the information about the last interrupt.
procAlgoResult : AlgoResult Sol Event Result -> IORef State -> IO ()
procAlgoResult algoRes r = do
  s <- readIORef r
  let putMsg = refreshMsgViewHtml (stMsgView s)
  case algoRes of
    Finish sol res => do
      (stNextBtn s) ?? remove
      modifyIORef r (record { stSol = sol, stLastInterrupt = Nothing })
      case res of
        Sat => putMsg "SAT"
        Unsat => putMsg "UNSAT - conflict clause on decision level 0"
    Interrupt sol e k => do
      modifyIORef r (record { stSol = sol, stLastInterrupt = Just (e, k) })
      case e of
        EDecide lit => putMsg $ "Decision: satisfy " ++ litToHtml lit
        EProp lit cl =>
          putMsg $ "Propagation: clause "
            ++ clauseToHtml cl
            ++ " forces "
            ++ litToHtml lit
        EConfl cl =>
          putMsg $ "Conflict clause "
            ++ clauseToHtml cl
            ++ " detected"
        ELearn cl =>
          putMsg $ "Learning: add asserting clause "
            ++ clauseToHtml cl
        EBacktrack lit _ => putMsg $ "Backtracking: undo " ++ litToHtml lit

-- Updates the visualization to correspond to the current state.
-- Runs the solver and updates the message with the description
-- of what the solver did.
next : IORef State -> IO ()
next r = do
  s <- readIORef r
  case stLastInterrupt s of
    Nothing => return ()
    Just (e, k) => do
      refreshClauseView
        (stClauseView s)
        (sClauses $ stSol $ s)
        (sTrail $ stSol $ s)
      refreshAssigView
        (stAssigView s)
        (sClauses $ stSol s)
        (sTrail $ stSol s)
      procAlgoResult (resume (stSol s) k) r

init : Sel NoData NoData -> IO ()
init parent = do
  msgView <- parent ?? createMsgView "msgView"

  clauseView <- parent ?? createClauseView "clauseView"

  assigView <- parent ?? createAssigView "assigView"

  addClauseBtn <- parent ?? append "input" >=>
                    classed "addClauseBtn" True >=>
                    attr "type" "button" >=>
                    property "value" "Add clause"

  startVisBtn <- parent ?? append "input" >=>
                   classed "startVisBtn" True >=>
                   attr "type" "button" >=>
                   property "value" "Start visualization"

  r <- newIORef $ MkState
         emptySol
         Nothing
         msgView
         clauseView
         assigView
         addClauseBtn
         startVisBtn
         d3 -- Dummy.

  addClauseBtn `onClick` \() => do
    litsStr <- prompt "Enter clause"
    s <- readIORef r
    case pure parseLits <$> litsStr of
      -- Prompt cancelled by user.
      Nothing => return ()
      -- Literals cannot be parsed.
      Just (Left err) =>
        refreshMsgView (stMsgView s) $ "Cannot parse literals: " ++ err
      -- Literals are ok, add clause.
      Just (Right lits) => do
        case run (stSol s) (addClause lits) of
          Interrupt _ _ _ =>
            putStrLn "Internal error: unexpected interrupt when adding clause"
          Finish sol _ => do
            modifyIORef r (record { stSol = sol })
            refreshClauseView (stClauseView s) (sClauses sol) (sTrail sol)
            refreshMsgView (stMsgView s) ""

  startVisBtn `onClick` \() => do
    s <- readIORef r
    (stAddClauseBtn s) ?? remove
    (stStartVisBtn s) ?? remove

    nextBtn <- parent ?? append "input" >=>
                 classed "nextBtn" True >=>
                 attr "type" "button" >=>
                 property "value" "Next"
    nextBtn `onClick` \() => next r

    modifyIORef r (record { stNextBtn = nextBtn })

    procAlgoResult (run (stSol s) solve) r

main : IO ()
main =
  d3 ?? select "body" >=> init
