-- Copyright (c) 2013 Radek Micek

module Main

import Common
import D3

main : IO ()
main = do

  firstItem <- d3 ?? selectAll "ul" >=>
                 select "li"

  firstItem ??
    style "color" "red" >=>
    style "font-style" "italic"

  return ()
