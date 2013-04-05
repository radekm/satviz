-- Copyright (c) 2013 Radek Micek

module Main

import Common
import D3

main : IO ()
main = do
    let width = 400
    let height = 300

    a <- mkNode "a"
    b <- mkNode "b"
    c <- mkNode "c"
    d <- mkNode "d"
    nodesArr <- mkArray [a, b, c, d]

    ab <- mkLink a b ()
    bc <- mkLink b c ()
    ac <- mkLink a c ()
    ad <- mkLink a d ()
    linksArr <- mkArray [ab, bc, ac, ad]

    fl <- mkForceLayout width height
    fl ?? linkDistanceL 120 >=>
      chargeL (-300)

    putNodes fl nodesArr
    putLinks fl linksArr

    svg <- d3 ?? select "body" >=>
             append "svg" >=>
             attr "width" (show width) >=>
             attr "height" (show height) >=>
             style "border" "1px solid blue"

    -- Style for arrows.
    svg ?? append "svg:defs" >=>
      append "svg:marker" >=>
      attr "id" "arrow" >=>
      attr "viewBox" "0 -7 16 14" >=>
      attr "refX" "50" >=>
      attr "markerWidth" "14" >=>
      attr "markerHeight" "16" >=>
      attr "orient" "auto" >=>
      attr "fill" "green" >=>
      append "svg:path" >=>
      attr "d" "M0 -7 L16 0 L0 7"

    linkLayer <- svg ?? append "svg:g"
    nodeLayer <- svg ?? append "svg:g"

    nodes <- nodeLayer ?? selectAll "text" >=>
               bind nodesArr
    nodes ?? enter >=>
      append "svg:text" >=>
      text' (const . getNData)

    links <- linkLayer ?? selectAll "line" >=>
               bind linksArr
    links ?? enter >=>
      append "svg:line" >=>
      style "stroke" "red" >=>
      style "stroke-width" "1px" >=>
      attr "marker-end" "url(#arrow)"

    fl `onTickL` tickHandler nodes links
    startL fl

    return ()
  where
    tickHandler :
      Sel NoData (Node String) ->
      Sel NoData (Link String ()) ->
      () -> IO ()
    tickHandler nodes links () = do
      nodes ??
        attr' "x" (\d, i => pure show <$> getX d) >=>
        attr' "y" (\d, i => pure show <$> getY d)
      links ??
        attr' "x1" (\d, i => getSource d >>= getX >>= pure . show) >=>
        attr' "y1" (\d, i => getSource d >>= getY >>= pure . show) >=>
        attr' "x2" (\d, i => getTarget d >>= getX >>= pure . show) >=>
        attr' "y2" (\d, i => getTarget d >>= getY >>= pure . show)
      return ()
