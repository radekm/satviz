-- Copyright (c) 2013 Radek Micek

module Main

import Common
import D3

main : IO ()
main = do
  xs <- mkArray ["cat", "dog"]
  ys <- mkArray ["oak", "birch", "maple"]
  arr <- mkArray [xs, ys]

  items <- d3 ?? selectAll "body > ul" >=>
             bind arr  >=>
             selectAll "body > ul > li" >=>
             bind' (\a, i => return a)

  items ?? style "background-color" "orange"
  items ?? enter >=>
    append "li" >=>
    text "New item:" >=>
    style "background-color" "green" >=>
    append "ul" >=>
    append "li"
  items ?? exit >=>
    style "background-color" "red"

  items ?? select "ul" >=>
    select "li" >=>
    text' (\str, i => return $ str ++ "/" ++ show i)

  return ()
