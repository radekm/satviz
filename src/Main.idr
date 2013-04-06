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
-- Implication graph view

data Vertex
  = VLit Lit

instance Eq Vertex where
  (VLit l) == (VLit l') = l == l'

instance Show Vertex where
  show (VLit l) = show l

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

  svg ?? append "svg:defs" >=>
    append "svg:marker" >=>
    attr "id" "arrow" >=>
    attr "viewBox" "0 -4 9 8" >=>
    attr "refX" "13" >=>
    attr "markerWidth" "9" >=>
    attr "markerHeight" "8" >=>
    attr "orient" "auto" >=>
    append "svg:path" >=>
    attr "d" "M0 -4 L9 0 L0 4"

  [| MkImplGraphView
       (mkForceLayout width height >>=
          linkDistanceL 100 >>=
          chargeL (-300))
       (svg ?? append "svg:g")
       (svg ?? append "svg:g")
       (svg ?? append "svg:g")
  |]

refreshImplGraphView : ImplGraphView -> List Clause -> Trail -> IO ()
refreshImplGraphView
  (MkImplGraphView fl linkLayer nodeLayer textLayer)
  clauses
  trail = do

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

    -- Add new links.
    newEdges <- filterM (edgeInView links >=> pure . not)
                  $ concatMap edgesLeadingToLit trail
    mapM_
      (mapTupleM (findNode nodes) >=>
         flip (uncurry mkLink) () >=>
         pushA links)
      newEdges

    putNodes fl nodes
    putLinks fl links

    --
    -- Bind arrays.
    --

    lines <- linkLayer ?? selectAll "line" >=>
               bindK links (const . linkKey)
    lines ?? exit >=> remove
    lines ?? enter >=>
      append "svg:line" >=>
      attr "marker-end" "url(#arrow)"

    circles <- nodeLayer ?? selectAll "circle" >=>
                 bindK nodes (const . nodeKey)
    circles ?? exit >=> remove
    circles ?? enter >=>
      append "svg:circle" >=>
      makeDraggableL fl >=>
      attr "r" "5"
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
    vertInModel v = isJust $ find ((== v) . toVert) trail
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

    linkKey : Link Vertex () -> IO String
    linkKey link = do
      (v, v') <- getEdge link
      return $ show v ++ "--->" ++ show v'
    nodeKey : Node Vertex -> IO String
    nodeKey = getVertex >=> pure . show
    vertClass : Vertex -> String
    vertClass (VLit (MkLit _ var)) = case findInTrail var trail of
                                       Just (_, Nothing, _) => "decided"
                                       Just (_, Just _, _) => "forced"
                                       Nothing => "error"
    vertLabel : Vertex -> IO String
    vertLabel (VLit l) = decodeEntities $ litToHtml l

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
        attr' "x" (const . (getX >=> pure . show . (+ 8))) >=>
        attr' "y" (const . (getY >=> pure . show . (+ 8)))
      return ()

-- ---------------------------------------------------------------------------

record State : Type where
  MkState :
    (stSol : Sol) ->
    (stLastInterrupt : Maybe (Event, Sol -> AlgoResult Sol Event Result)) ->
    (stMsgView : MsgView) ->
    (stClauseView : ClauseView) ->
    (stAssigView : AssigView) ->
    (stImplGraphView : ImplGraphView) ->
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
        (sClauses $ stSol s)
        (sTrail $ stSol s)
      refreshAssigView
        (stAssigView s)
        (sClauses $ stSol s)
        (sTrail $ stSol s)
      refreshImplGraphView
        (stImplGraphView s)
        (sClauses $ stSol s)
        (sTrail $ stSol s)
      procAlgoResult (resume (stSol s) k) r

init : Sel NoData NoData -> IO ()
init parent = do
  msgView <- parent ?? createMsgView "msgView"

  clauseView <- parent ?? createClauseView "clauseView"

  assigView <- parent ?? createAssigView "assigView"

  implGraphView <- parent ?? createImplGraphView "implGraphView" 600 418

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
         implGraphView
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
