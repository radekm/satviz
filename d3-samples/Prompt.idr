-- Copyright (c) 2013 Radek Micek

module Main

import Common
import D3

main : IO ()
main = do
  btn <- d3 ?? select "body" >=>
           append "input" >=>
           attr "type" "button" >=>
           property "value" "Show prompt"

  log <- d3 ?? select "body" >=>
           append "ul"

  btn `onClick` \() => do
    res <- prompt "Enter some text"
    let msg = case res of
                Nothing => "Prompt cancelled"
                Just s => "Entered text: " ++ s
    log ?? append "li" >=> text msg
    return ()
