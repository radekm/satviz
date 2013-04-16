-- Copyright (c) 2013 Radek Micek

module Algo

-- s - state, i - reason of interruption, r - result of whole computation.
data AlgoResult s i r
  = Interrupt s i (s -> AlgoResult s i r)
  | Finish s r

data Algo s i r a
  = MkAlgo (s -> (a -> s -> AlgoResult s i r) -> AlgoResult s i r)

runAlgo : Algo s i r a -> s -> (a -> s -> AlgoResult s i r) -> AlgoResult s i r
runAlgo (MkAlgo x) = x

algoReturn : a -> Algo s i r a
algoReturn a = MkAlgo $ \s, k => k a s

algoBind : Algo s i r a -> (a -> Algo s i r b) -> Algo s i r b
algoBind x f = MkAlgo $ \s, k =>
  runAlgo x s (\a, s' => runAlgo (f a) s' k)

instance Functor (Algo s i r) where
  fmap f x = algoBind x (\x' => algoReturn (f x'))

instance Applicative (Algo s i r) where
  pure = algoReturn
  f <$> x =
    algoBind f (\f' =>
    algoBind x (\x' =>
    algoReturn (f' x')))

instance Monad (Algo s i r) where
  return = algoReturn
  (>>=) = algoBind

run : s -> Algo s i r r -> AlgoResult s i r
run s x = runAlgo x s (\r, s' => Finish s' r)

interrupt : i -> Algo s i r ()
interrupt i = MkAlgo $ \s, k => Interrupt s i (k ())

resume : s -> (s -> AlgoResult s i r) -> AlgoResult s i r
resume s k = k s

put : s -> Algo s i r ()
put s = MkAlgo $ \_, k => k () s

get : Algo s i r s
get = MkAlgo $ \s, k => k s s
