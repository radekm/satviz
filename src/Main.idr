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
      html' (\lit, i => return $ litHtml lit) >=>
      attr' "class" (\lit, i => return $ litClass $ assig lit)

    return ()
  where
    litHtml : Lit -> String
    litHtml (MkLit Pos lit) = lit
    litHtml (MkLit Neg lit) = "&#172;" ++ lit
    litClass : LBool -> String
    litClass LTrue = "sat"
    litClass LFalse = "unsat"
    litClass LUndef = "unassigned"

-- ---------------------------------------------------------------------------

record State : Type where
  MkState :
    (stSol : Sol) ->
    (stMsgView : MsgView) ->
    (stClauseView : ClauseView) ->
    (stAddClauseBtn : Sel NoData NoData) ->
    State

init : Sel NoData NoData -> IO ()
init parent = do
  msgView <- parent ?? createMsgView "msgView"

  clauseView <- parent ?? createClauseView "clauseView"

  addClauseBtn <- parent ?? append "input" >=>
                    classed "addClauseBtn" True >=>
                    attr "type" "button" >=>
                    property "value" "Add clause"

  r <- newIORef $ MkState
         emptySol
         msgView
         clauseView
         addClauseBtn

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

main : IO ()
main =
  d3 ?? select "body" >=> init
