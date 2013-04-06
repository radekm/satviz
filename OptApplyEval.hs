-- Copyright (c) 2013 Radek Micek
--
-- This file is distributed under the terms of the MIT License.


-- Usage: OptApplyEval unoptimized.js optimized.js
--
-- Optimizes functions __IDR__.APPLY0 and __IDR__.EVAL0 by converting
-- the large if-else statement to switch.


import Data.List
import Control.Applicative
import System.Environment

main :: IO ()
main = do
  [input, output] <- take 2 <$> getArgs
  ls <- lines <$> readFile input
  let (before, apply0, eval0, after) = splitLines ls
  writeFile output $ unlines $ concat
    [ before
    , procApply apply0
    , procEval eval0
    , after
    ]

splitLines :: [String] -> ([String], [String], [String], [String])
splitLines ls = (before, apply0, eval0, after)
  where
    (before, ls2)  = break (== "__IDR__.APPLY0 = function(fn0,arg0){") ls
    (apply0, ls3)  = break (== "__IDR__.EVAL0 = function(arg0){") ls2
    (eval0', ls4') = break (== "};") ls3 -- Line "};" belongs to eval0.
    (eval0, after) = (eval0' ++ ["};"], tail ls4')

procApply :: [String] -> [String]
procApply = concatMap f
  where
    f l
      | "if (e instanceof __IDRRT__.Con && " `isPrefixOf` l
      = [ "if (e instanceof __IDRRT__.Con)"
        , "switch (e.i) {"
        , "case " ++ numStr ++ ":"
        ]
      | "} else if (e instanceof __IDRRT__.Con && " `isPrefixOf` l
      = ["case " ++ numStr ++ ":"]
      | otherwise
      = [l]
      where
        numStr = filter (`elem` ['0'..'9']) l

procEval :: [String] -> [String]
procEval = concatMap f
  where
    f l
      | "if (e instanceof __IDRRT__.Con && " `isPrefixOf` l
      = [ "if (!(e instanceof __IDRRT__.Con)) {"
        , "return __var_0;"
        , "} else"
        , "switch (e.i) {"
        , "case " ++ numStr ++ ":"
        ]
      | "} else if (e instanceof __IDRRT__.Con && " `isPrefixOf` l
      = ["case " ++ numStr ++ ":"]
      | "} else if (true) {" `isPrefixOf` l
      = ["default:"]
      | otherwise
      = [l]
      where
        numStr = filter (`elem` ['0'..'9']) l
