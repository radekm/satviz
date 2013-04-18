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

strong : String -> String
strong s = "<strong>" ++ s ++ "</strong>"

litToHtml : Lit -> String
litToHtml (MkLit Pos lit) = lit
litToHtml (MkLit Neg lit) = "&#172;" ++ lit

clauseToHtml' : List Lit -> String
clauseToHtml' lits =
  case lits of
    [] => "&#9633;"
    ls => mconcat $ intersperse " &#8744; " $ map litToHtml ls

clauseToHtml : Clause -> String
clauseToHtml (MkClause _ lits) = clauseToHtml' lits

litListToHtml : List Lit -> String
litListToHtml lits =
  "[" ++ (mconcat $ intersperse ", " $ map litToHtml lits) ++ "]"

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

refreshClauseView :
  ClauseView ->
  List Clause ->
  Trail ->
  List (CId, (Lit, Lit)) ->
  Operation ->
  IO ()
refreshClauseView (MkClauseView v) clauseList trail watched operation = do
    clauseArr <- mkArray clauseList

    let assig = trailToAssig trail

    clauses <- v ?? selectAll "ul.clauseViewRoot > li" >=>
               bind clauseArr
    clauses ?? exit >=> remove
    clauses ?? enter >=>
      append "li" >=>
      append "ul"
    clauses ??
      attr' "class" (const . pure . clauseClass)

    lits <- clauses ?? select "ul" >=>
              selectAll "li" >=>
              bind' (\d, i => mkArray $ map (\l => (getCId d, l)) $ getLits d)
    lits ?? exit >=> remove
    lits ?? enter >=>
      append "li" >=>
      append "span"

    lits ??
      attr' "class" (\cidLit, i => return $ litClass cidLit assig) >=>
      select "span" >=>
      html' (\cidLit, i => return $ litToHtml $ snd cidLit)

    return ()
  where
    getCId : Clause -> CId
    getCId (MkClause cid _) = cid
    clauseClass : Clause -> String
    clauseClass (MkClause cid _) =
      case operation of
        OPropagate before (cur :: after) =>
          if cid `clElem` before then
            "before"
          else if cid `clElem` [cur] then
            "cur"
          else if cid `clElem` after then
            "after"
          else
            ""
        -- All clauses are processed.
        OPropagate before [] =>
          if cid `clElem` before then
            "before"
          else
            ""
        _ => ""
      where
        clElem : CId -> List Clause -> Bool
        clElem cid' cs = isJust $ find ((== cid') . getCId) cs
    litClass : (CId, Lit) -> Assignment -> String
    litClass (cid, lit) assig =
      case assig lit of
        LTrue => "sat" ++ watchedCls
        LFalse => "unsat" ++ watchedCls
        LUndef => "unassigned" ++ watchedCls
      where
        watchedCls : String
        watchedCls = case find (\(cid', _) => cid' == cid) watched of
                       Nothing => ""
                       Just (_, (l, l')) =>
                         if lit == negLit l || lit == negLit l' then
                           " watched"
                         else
                           ""

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
-- Implication graph view

data Vertex
  = VLit Lit
  | VConfl

instance Eq Vertex where
  (VLit l) == (VLit l') = l == l'
  VConfl   == VConfl    = True
  _        == _         = False

instance Show Vertex where
  show (VLit l) = show l
  show VConfl = "?K"

Edge : Type
Edge = (Vertex, Vertex)

getVertex : Node Vertex -> IO Vertex
getVertex = getNData

getEdge : Link Vertex () -> IO Edge
getEdge = getSrcTgt >=> mapTupleM getVertex

data ImplGraphView
  = MkImplGraphView
      (ForceLayout Vertex ())
      (Sel NoData NoData) -- Link layer.
      (Sel NoData NoData) -- Node layer.
      (Sel NoData NoData) -- Text layer.

createImplGraphView : String -> Float -> Float -> Sel a b -> IO ImplGraphView
createImplGraphView cssClass width height parent = do

  svg <- parent ?? append "svg" >=>
           forgetBoundData >=>
           attr "width" (show width) >=>
           attr "height" (show height) >=>
           classed cssClass True

  let setupMarker =
    attr "viewBox" "0 -4 9 8" >=>
    attr "refX" "16" >=>
    attr "markerWidth" "9" >=>
    attr "markerHeight" "8" >=>
    attr "orient" "auto" >=>
    append "svg:path" >=>
    attr "d" "M0 -4 L9 0 L0 4"

  defs <- svg ?? append "svg:defs"
  defs ?? append "svg:marker" >=>
    attr "id" "arrow" >=>
    setupMarker
  defs ?? append "svg:marker" >=>
    attr "id" "arrowCut" >=>
    attr "fill" "#00f" >=>
    setupMarker
  defs ?? append "svg:marker" >=>
    attr "id" "arrowProc" >=>
    attr "fill" "#cc0000" >=>
    setupMarker
  defs ?? append "svg:marker" >=>
    attr "id" "arrowMinim" >=>
    attr "fill" "#cc0000" >=>
    setupMarker

  [| MkImplGraphView
       (mkForceLayout width height >>=
          linkDistanceL 100 >>=
          chargeL (-300))
       (svg ?? append "svg:g")
       (svg ?? append "svg:g")
       (svg ?? append "svg:g")
  |]

refreshImplGraphView :
  ImplGraphView ->
  List Clause ->
  Trail ->
  Operation ->
  IO ()
refreshImplGraphView
  (MkImplGraphView fl linkLayer nodeLayer textLayer)
  clauses
  trail
  operation = do

    stopL fl

    --
    -- Update arrays with nodes and links.
    --

    -- Remove old nodes and links.
    nodes <- getNodes fl >>= filterA (getVertex >=> pure . vertInModel)
    links <- getLinks fl >>=
               filterA (getEdge >=>
                        mapTupleM (vertInView nodes) >=>
                        pure . uncurry (&&))

    -- Add new nodes.
    newVertices <- filterM (vertInView nodes >=> pure . not)
                     $ map toVert trail
    mapM_ (mkNode >=> pushA nodes) newVertices
    addConfl nodes

    -- Add new links.
    newEdges <- filterM (edgeInView links >=> pure . not)
                  $ concatMap edgesLeadingToLit trail
    mapM_
      (mapTupleM (findNode nodes) >=>
         flip (uncurry mkLink) () >=>
         pushA links)
      newEdges
    addLinksToConfl nodes links

    putNodes fl nodes
    putLinks fl links

    --
    -- Bind arrays.
    --

    lines <- linkLayer ?? selectAll "line" >=>
               bindK links (const . linkKey)
    lines ?? exit >=> remove
    lines ?? enter >=> append "svg:line"
    lines ??
      attr' "class" (const . (getEdge >=> pure . edgeClass)) >=>
      attr' "marker-end" (const . (getEdge >=> pure . edgeMarkerEnd)) >=>
      attr' "stroke-dasharray" (const . (getEdge >=> pure . edgeDashArray))

    circles <- nodeLayer ?? selectAll "circle" >=>
                 bindK nodes (const . nodeKey)
    circles ?? exit >=> remove
    circles ?? enter >=>
      append "svg:circle" >=>
      makeDraggableL fl >=>
      attr "r" "7"
    circles ?? attr' "class" (const . (getVertex >=> pure . vertClass))

    textGroups <- textLayer ?? selectAll "g" >=>
                    bindK nodes (const . nodeKey)
    textGroups ?? exit >=> remove
    newTextGroups <- textGroups ?? enter >=> append "svg:g"

    -- Shadow.
    newTextGroups ?? append "svg:text" >=>
      attr "class" "shadow" >=>
      text' (const . (getVertex >=> vertLabel))

    -- Text.
    newTextGroups ?? append "svg:text" >=>
      text' (const . (getVertex >=> vertLabel))

    labels <- textGroups ?? selectAll "text" >=>
                forgetBoundData >=>
                castBoundData

    --
    -- Tick handler.
    --

    fl `onTickL` tickHandler lines circles labels

    startL fl
  where
    toVert : (Lit, Maybe Ante, Level) -> Vertex
    toVert (lit, _, _) = VLit lit
    vertInModel : Vertex -> Bool
    vertInModel v = case v of
                      VLit _ => isJust $ find ((== v) . toVert) trail
                      VConfl => case operation of
                                  OLearn _ _ _ => True
                                  _ => False
    vertInView : Array (Node Vertex) -> Vertex -> IO Bool
    vertInView ns v = anyA (getVertex >=> pure . (== v)) ns
    edgesLeadingToLit : (Lit, Maybe Ante, Level) -> List Edge
    edgesLeadingToLit (_, Nothing, _) = []
    edgesLeadingToLit (lit, Just cid, _) =
      -- Source literal is negated since it is assigned false.
      map (\l => (VLit $ negLit l, VLit lit))
        -- No edge from itself.
        $ filter (/= lit)
        $ getLits
        $ findClause cid clauses
    edgeInView : Array (Link Vertex ()) -> Edge -> IO Bool
    edgeInView ls e = anyA (getEdge >=> pure . (== e)) ls
    findNode : Array (Node Vertex) -> Vertex -> IO (Node Vertex)
    findNode ns v =
      fromJust `fmap` findA (getVertex >=> pure . (== v)) ns
    addConfl : Array (Node Vertex) -> IO ()
    addConfl ns = do
      inView <- vertInView ns VConfl
      if not inView && vertInModel VConfl then
        mkNode VConfl >>= pushA ns
      else
        return ()
    addLinksToConfl : Array (Node Vertex) -> Array (Link Vertex ()) -> IO ()
    addLinksToConfl ns ls =
      case operation of
        OLearn _ (MkClause _ lits) _ => do
          newEdges <- filterM (edgeInView ls >=> pure . not)
                        $ map (\l => (VLit $ negLit l, VConfl)) lits
          mapM_
            (mapTupleM (findNode ns) >=>
               flip (uncurry mkLink) () >=>
               pushA ls)
            newEdges
        _ => return ()

    linkKey : Link Vertex () -> IO String
    linkKey link = do
      (v, v') <- getEdge link
      return $ show v ++ "--->" ++ show v'
    nodeKey : Node Vertex -> IO String
    nodeKey = getVertex >=> pure . show
    isInConflClause : List Lit -> Vertex -> Bool
    isInConflClause _ VConfl = False
    isInConflClause conflCl (VLit (MkLit _ var)) =
      isJust $ find (\(MkLit _ v) => v == var) conflCl
    isProc : List Var -> Vertex -> Bool
    isProc _ VConfl = True
    isProc vars (VLit (MkLit _ var)) = isJust $ find (== var) vars
    edgeCase : String -> String -> String -> String -> Edge -> String
    edgeCase normal cut proc minim (src, tgt) =
      case operation of
        OLearn conflCl _ vars =>
          if isProc vars src then
            proc
          else if isInConflClause conflCl src && isProc vars tgt then
            cut
          else
            normal
        OMinimize lits =>
          case (src, tgt) of
            (VLit s, VLit t) =>
              if (s `elem` lits) && (t `elem` lits) then
                minim
              else
                normal
            _ => "error"
        _ => normal
    edgeCase _ _ _ _ (VConfl, _) = "error"
    edgeClass : Edge -> String
    edgeClass = edgeCase "" "cut" "proc" "minim"
    edgeMarkerEnd : Edge -> String
    edgeMarkerEnd = edgeCase
                      "url(#arrow)"
                      "url(#arrowCut)" "url(#arrowProc)"
                      "url(#arrowMinim)"
    edgeDashArray : Edge -> String
    edgeDashArray = edgeCase "" "" "4, 4" ""
    vertClass : Vertex -> String
    vertClass (VLit (MkLit s var)) = cls ++ opCls
      where
        v : Vertex
        v = VLit $ MkLit s var
        cls = case findInTrail var trail of
                Just (_, Nothing, _) => "decided"
                Just (_, Just _, _) => "forced"
                Nothing => "error"
        opCls = case operation of
                  OLearn conflCl _ vars =>
                    if isProc vars v then
                      " proc"
                    else if isInConflClause conflCl v then
                      " inConflClause"
                    else
                      ""
                  OMinimize lits =>
                    if (MkLit s var) `elem` lits then
                      " minim"
                    else
                      ""
                  _ => ""
    vertClass VConfl = "conflVertex"
    vertLabel : Vertex -> IO String
    vertLabel (VLit l) = decodeEntities $ litToHtml l
    vertLabel VConfl = return "K"

    tickHandler :
      Sel NoData (Link Vertex ()) ->
      Sel NoData (Node Vertex) ->
      Sel NoData (Node Vertex) ->
      () -> IO ()
    tickHandler lines circles labels () = do
      lines ??
        attr' "x1" (const . (getSource >=> getX >=> pure . show)) >=>
        attr' "y1" (const . (getSource >=> getY >=> pure . show)) >=>
        attr' "x2" (const . (getTarget >=> getX >=> pure . show)) >=>
        attr' "y2" (const . (getTarget >=> getY >=> pure . show))
      circles ??
        attr' "cx" (const . (getX >=> pure . show)) >=>
        attr' "cy" (const . (getY >=> pure . show))
      labels ??
        attr' "x" (const . (getX >=> pure . show . (+ 10))) >=>
        attr' "y" (const . (getY >=> pure . show . (+ 10)))
      return ()

-- ---------------------------------------------------------------------------
-- Check box

data CheckBox = MkCheckBox (Sel NoData NoData)

createCheckBox : String -> String -> Bool -> Sel a b -> IO CheckBox
createCheckBox cssClass label checked parent = do
  cb <- parent ?? append "span" >=>
          forgetBoundData >=>
          classed cssClass True >=>
          classed "checkBoxRoot" True
  cb ?? append "input" >=>
    attr "type" "checkbox" >=>
    boolProperty "checked" checked
  cb ?? append "span" >=>
    text label
  return $ MkCheckBox cb

isChecked : CheckBox -> IO Bool
isChecked (MkCheckBox cb) =
  cb ?? select "input" >=>
    getBoolProperty "checked"

setChecked : CheckBox -> Bool -> IO ()
setChecked (MkCheckBox cb) checked = do
  cb ?? select "input" >=>
    boolProperty "checked" checked
  return ()

removeCheckBox : CheckBox -> IO ()
removeCheckBox (MkCheckBox cb) = cb ?? remove

-- ---------------------------------------------------------------------------

record State : Type where
  MkState :
    (stSol : Sol) ->
    (stSolHist : List Sol) ->
    (stAutoAssig : Bool) ->
    (stConflAnalVis : Bool) ->
    (stLastInterrupt : Maybe (Event, Sol -> AlgoResult Sol Event Result)) ->
    (stInterruptHist : List (Event, Sol -> AlgoResult Sol Event Result)) ->
    (stMsgView : MsgView) ->
    (stClauseView : ClauseView) ->
    (stAssigView : AssigView) ->
    (stImplGraphView : ImplGraphView) ->
    (stAddClauseBtn : Sel NoData NoData) ->
    (stStartVisBtn : Sel NoData NoData) ->
    (stPrevBtn : Sel NoData NoData) ->
    (stNextBtn : Sel NoData NoData) ->
    State

consMaybe : Maybe a -> List a -> List a
consMaybe Nothing xs = xs
consMaybe (Just x) xs = x :: xs

-- Updates the message and the information about the last interrupt.
procAlgoResult : AlgoResult Sol Event Result -> IORef State -> IO ()
procAlgoResult algoRes r = do
  s <- readIORef r
  let origSol = stSol s
  let origLastInterrupt = stLastInterrupt s
  let origSolHist = stSolHist s
  let origInterruptHist = stInterruptHist s
  let putMsg = refreshMsgViewHtml (stMsgView s)
  let funcs = ( strong . litToHtml
              , strong . clauseToHtml'
              , strong . clauseToHtml
              , strong . litListToHtml )
  let (lit2Html, clause2Html', clause2Html, litList2Html) = funcs
  let revertState = (record { stSol = origSol
                            , stSolHist = origSolHist
                            , stLastInterrupt = origLastInterrupt
                            , stInterruptHist = origInterruptHist })
  modifyIORef r (record { stSolHist = origSol :: origSolHist
                        , stInterruptHist = consMaybe
                                              origLastInterrupt
                                              origInterruptHist })
  case algoRes of
    Finish sol res => do
      (stNextBtn s) ?? style "display" "none" >=>
        (\x => return ()) -- Change result type to satisfy the compiler.
      modifyIORef r (record { stSol = sol, stLastInterrupt = Nothing })
      case res of
        Sat => putMsg "SAT"
        Unsat => putMsg "UNSAT - conflict clause on decision level 0"
    Interrupt sol e k => do
      modifyIORef r (record { stSol = sol, stLastInterrupt = Just (e, k) })
      case e of
        EChoose (v :: _) =>
          if stAutoAssig s then do
            -- Place automatically chosen literal into the solver.
            let sol2 = record { sChosen = Just $ MkLit Pos v } sol
            -- Don't save current sol and interrupt into history.
            modifyIORef r revertState
            procAlgoResult (resume sol2 k) r
          else
            putMsg $ "Choose unassigned literal to be satisfied"
        EDecide lit => putMsg $ "Decision: satisfy " ++ lit2Html lit
        EProp lit cl =>
          putMsg $ "Propagation: clause "
            ++ clause2Html cl
            ++ " forces "
            ++ lit2Html lit
        EConfl cl =>
          putMsg $ "Conflict clause "
            ++ clause2Html cl
            ++ " detected"
        EWShortClause l cl =>
          putMsg $ "Propagation: satisfy "
            ++ lit2Html l
        EWPropLitStart l =>
          putMsg $ "Propagation: process clauses where "
            ++ lit2Html l
            ++ " is watched"
        EWOtherLitTrue l l' cl =>
          putMsg $ "Propagation: skip clause "
            ++ clause2Html cl
            ++ " because other watched literal "
            ++ lit2Html l'
            ++ " is true"
        EWReplaceLit oldL newL cl =>
          putMsg $ "Propagation: replace watched literal "
            ++ lit2Html oldL
            ++ " by "
            ++ lit2Html newL
            ++ " in clause "
            ++ clause2Html cl
        EWConfl l l' cl =>
          putMsg $ "Propagation: literal "
            ++ lit2Html l
            ++ " watched in clause "
            ++ clause2Html cl
            ++ " cannot be replaced and other watched literal "
            ++ lit2Html l'
            ++ " is false"
        EWProp l l' cl =>
          putMsg $ "Propagation: literal "
            ++ lit2Html l
            ++ " watched in clause "
            ++ clause2Html cl
            ++ " cannot be replaced, so other watched literal "
            ++ lit2Html l'
            ++ " is forced"
        EAnalyzeStart cl =>
          if stConflAnalVis s then
            putMsg $ "Analysis: make asserting clause "
              ++ "from current conflict clause " ++ clause2Html cl
          else do
            -- Don't save current sol and interrupt into history.
            modifyIORef r revertState
            procAlgoResult (resume sol k) r
        EResolve v conflCl anteCl resolvent =>
          if stConflAnalVis s then
            putMsg $ "Analysis: resolve current conflict clause "
              ++ clause2Html' conflCl
              ++ " with " ++ clause2Html anteCl
              ++ " on variable " ++ strong v
              ++ " and form new conflict clause "
              ++ clause2Html' resolvent
          else do
            -- Don't save current sol and interrupt into history.
            modifyIORef r revertState
            procAlgoResult (resume sol k) r
        ESkip v conflCl anteCl =>
          if stConflAnalVis s then
            putMsg $ "Analysis: variable "
              ++ strong v ++ " is not present in current conflict clause "
              ++ clause2Html' conflCl
          else do
            -- Don't save current sol and interrupt into history.
            modifyIORef r revertState
            procAlgoResult (resume sol k) r
        EAnalyzeEnd cl =>
          if stConflAnalVis s then
            putMsg $ "Analysis: found asserting clause "
              ++ clause2Html' cl
          else do
            -- Don't save current sol and interrupt into history.
            modifyIORef r revertState
            procAlgoResult (resume sol k) r
        EMinStart candidates assertingCl =>
          putMsg $ "Minimization:"
            ++ " remove redundant literals from asserting clause "
            ++ clause2Html' assertingCl
            ++ "; candidates for removal are "
            ++ litList2Html candidates
        ETestRedundant l assertingCl =>
          putMsg $ "Minimization:"
            ++ " test whether literal "
            ++ lit2Html l
            ++ " is redundant in asserting clause "
            ++ clause2Html' assertingCl
        ERedundant l assertingCl =>
          putMsg $ "Minimization:"
            ++ " literal "
            ++ lit2Html l
            ++ " is redundant in asserting clause "
            ++ clause2Html' assertingCl
        ENotRedundant l assertingCl =>
          putMsg $ "Minimization:"
            ++ " literal "
            ++ lit2Html l
            ++ " isn't redundant in asserting clause "
            ++ clause2Html' assertingCl
        EMinEnd redundantLits assertingCl minAssertingCl =>
          putMsg $ "Minimization:"
            ++ " remove redundant literals "
            ++ litList2Html redundantLits
            ++ " from asserting clause "
            ++ clause2Html' assertingCl
            ++ " and form new asserting clause "
            ++ clause2Html' minAssertingCl
        ELearn cl =>
          putMsg $ "Learning: add asserting clause "
            ++ clause2Html cl
        EBacktrack lit _ => putMsg $ "Backtracking: undo " ++ lit2Html lit

refreshClauseAssigImplGraphViews : IORef State -> Sol -> IO ()
refreshClauseAssigImplGraphViews r sol = do
  s <- readIORef r
  refreshClauseView
    (stClauseView s)
    (sClauses sol)
    (sTrail sol)
    (sWatched sol)
    (sOp sol)
  refreshAssigView
    (stAssigView s)
    (sClauses sol)
    (sTrail sol)
  refreshImplGraphView
    (stImplGraphView s)
    (sClauses sol)
    (sTrail sol)
    (sOp sol)

-- Updates the visualization to correspond to the current state.
-- Runs the solver and updates the message with the description
-- of what the solver did.
next : IORef State -> IO ()
next r = do
  s <- readIORef r
  let sol = stSol s
  case stLastInterrupt s of
    Nothing => return ()
    Just (e, k) => do
      refreshClauseAssigImplGraphViews r sol
      case e of
        EChoose vars => do
          litStr <- prompt "Choose literal to be satisfied"
          case pure parseLit <$> litStr of
            Just (Right (MkLit sign v)) =>
              if v `elem` vars then do
                (stPrevBtn s) ?? style "display" "block" >=>
                  (\x => return ()) -- Change result type to satisfy the compiler.
                -- Place chosen literal into the solver.
                let sol2 = record { sChosen = Just $ MkLit sign v } sol
                procAlgoResult (resume sol2 k) r
              else
                return ()
            _ =>
              return ()
        _ => do
          (stPrevBtn s) ?? style "display" "block" >=>
            (\x => return ()) -- Change result type to satisfy the compiler.
          procAlgoResult (resume sol k) r

prev : IORef State -> IO ()
prev r = do
  s <- readIORef r
  case stInterruptHist s of
    [] => return ()
    (e, k) :: interruptHist => do
      -- Currently (hd $ stSolHist s) and (stLastInterrupt s) are visualized.
      let sol = hd $ tl $ stSolHist s
      refreshClauseAssigImplGraphViews r sol
      modifyIORef r (record { stSol = sol
                            , stSolHist = tl $ tl $ stSolHist s
                            , stLastInterrupt = head' interruptHist
                            , stInterruptHist = drop 1 interruptHist })
      (stNextBtn s) ?? style "display" "block" >=>
        (\x => return ()) -- Change result type to satisfy the compiler.
      if isNil interruptHist then
        (stPrevBtn s) ?? style "display" "none" >=>
          (\x => return ()) -- Change result type to satisfy the compiler.
      else
        return ()
      procAlgoResult (Interrupt (hd $ stSolHist s) e k) r
      return ()
    _ => return ()

initSolver : Sel NoData NoData -> (Bool, Bool, Bool, Bool) -> IO ()
initSolver parent (autoAssig, conflAnalVis, watchedLits, minClause) = do
  msgView <- parent ?? createMsgView "msgView"

  clauseView <- parent ?? createClauseView "clauseView"

  assigView <- parent ?? createAssigView "assigView"

  implGraphView <- parent ?? createImplGraphView "implGraphView" 600 468

  addClauseBtn <- parent ?? append "input" >=>
                    classed "addClauseBtn" True >=>
                    attr "type" "button" >=>
                    property "value" "Add clause"

  startVisBtn <- parent ?? append "input" >=>
                   classed "startVisBtn" True >=>
                   attr "type" "button" >=>
                   property "value" "Start visualization"

  r <- newIORef $ MkState
         (record { sEnableWatchedLits = watchedLits
                 , sEnableMinimization = minClause } emptySol)
         []
         autoAssig
         conflAnalVis
         Nothing -- Last interrupt.
         []
         msgView
         clauseView
         assigView
         implGraphView
         addClauseBtn
         startVisBtn
         d3 -- Dummy.
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
      -- Literals are ok.
      Just (Right lits) => do
        let lits' = nub lits
        let vars : List Var = map (\(MkLit _ v) => v) lits'
        if isNil lits' then
          refreshMsgView (stMsgView s) "Clause is ignored because it is empty"
        else if vars /= nub vars then
          refreshMsgViewHtml (stMsgView s) $ "Clause "
            ++ strong (clauseToHtml' lits')
            ++ " is ignored because it contains complementary literals"
        -- Add clause.
        else
          case run (stSol s) (addClause lits') of
            Interrupt _ _ _ =>
              putStrLn "Internal error: unexpected interrupt when adding clause"
            Finish sol _ => do
              modifyIORef r (record { stSol = sol })
              refreshClauseView
                (stClauseView s)
                (sClauses sol)
                (sTrail sol)
                (sWatched sol)
                (sOp sol)
              refreshMsgView (stMsgView s) ""

  startVisBtn `onClick` \() => do
    s <- readIORef r
    (stAddClauseBtn s) ?? remove
    (stStartVisBtn s) ?? remove

    prevBtn <- parent ?? append "input" >=>
                 classed "prevBtn" True >=>
                 attr "type" "button" >=>
                 property "value" "Prev" >=>
                 style "display" "none"
    prevBtn `onClick` \() => prev r

    nextBtn <- parent ?? append "input" >=>
                 classed "nextBtn" True >=>
                 attr "type" "button" >=>
                 property "value" "Next"
    nextBtn `onClick` \() => next r

    modifyIORef r (record { stPrevBtn = prevBtn
                          , stNextBtn = nextBtn })

    procAlgoResult (run (stSol s) solve) r

init : Sel NoData NoData -> IO ()
init parent = do
  cfg <- parent ?? append "div"

  autoAssigCB <- createCheckBox
                   "autoAssigCB"
                   "Automatic assignment"
                   True cfg

  conflAnalVisCB <- createCheckBox
                      "conflAnalVisCB"
                      "Conflict analysis visualization"
                      True cfg

  watchedLitsCB <- createCheckBox
                     "watchedLitsCB"
                     "Watched literals"
                     False cfg

  minClauseCB <- createCheckBox
                   "minClauseCB"
                   "Minimize asserting clause"
                   False cfg

  goOnBtn <- cfg ?? append "input" >=>
               classed "goOnBtn" True >=>
               attr "type" "button" >=>
               property "value" "Go on"

  goOnBtn `onClick` \() => do
    autoAssig <- isChecked autoAssigCB
    conflAnalVis <- isChecked conflAnalVisCB
    watchedLits <- isChecked watchedLitsCB
    minClause <- isChecked minClauseCB
    cfg ?? remove
    initSolver parent (autoAssig, conflAnalVis, watchedLits, minClause)

main : IO ()
main =
  d3 ?? select "body" >=> init
