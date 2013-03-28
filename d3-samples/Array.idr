-- Copyright (c) 2013 Radek Micek

module Main

import D3

-- Prints: 4, 3, 5, 0, 1, 17
main : IO ()
main = do
  arr <- mkArray [1, 2, 3, 6]
  pure print <$> lengthA arr

  pure print <$> getNth arr 2
  setNth arr 2 5
  pure print <$> getNth arr 2

  arr2 <- emptyA ()
  pure print <$> lengthA arr2
  pushA arr2 17
  pure print <$> lengthA arr2
  pure print <$> getNth arr2 0

  return ()
