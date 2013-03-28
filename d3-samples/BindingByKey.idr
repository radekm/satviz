-- Copyright (c) 2013 Radek Micek

module Main

import Common
import D3

data Item = MkItem String String

getKey : Item -> String
getKey (MkItem k _) = k

getValue : Item -> String
getValue (MkItem _ v) = v

main : IO ()
main = do
  let items : List Item =
    [ MkItem "a" "porch"
    , MkItem "d" "larder"
    , MkItem "b" "utility room"
    , MkItem "f" "shed"
    ]
  arr <- mkArray items

  d3 ?? select "ul" >=>
    selectAll "li" >=>
    bindK arr (\d, i => return $ getKey d)  >=>
    enter >=>
    append "li" >=>
    text' (\d, i => return $ getValue d)

  let items2 : List Item =
    [ MkItem "b" "Utility room"
    , MkItem "B" "kitchen"
    , MkItem "d" "Larder"
    ]
  arr2 <- mkArray items2

  li <- d3 ?? selectAll "ul" >=>
          bind' (\d, i => mkArray [arr2]) >=>
          selectAll "li" >=>
          bindK' (\d, i => return d) (\d, i => return $ getKey d)
  li ?? style "background-color" "orange"
  li ?? enter >=>
    append "li" >=>
    style "background-color" "green"
  li ?? exit >=>
    remove
  li ?? text' (\d, i => return $ getValue d)

  return ()
