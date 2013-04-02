-- Copyright (c) 2013 Radek Micek

module Main

import D3

main : IO ()
main = do

  -- Prints: 3, 5
  arr <- mkArray [1, 2, 3, 6]
  getNth arr 2 >>= print
  setNth arr 2 5
  getNth arr 2 >>= print

  -- Prints: 0, 1, 17
  arr2 <- emptyA ()
  lengthA arr2 >>= print
  pushA arr2 17
  lengthA arr2 >>= print
  getNth arr2 0 >>= print

  -- Prints: True, False
  anyA (== 5) arr >>= print
  anyA (== 3) arr >>= print

  -- Prints: [1, 2, 5, 6]
  --         [1, 2]
  arr3 <- filterA (< 4) arr
  arrayToList arr >>= print
  arrayToList arr3 >>= print

  return ()
