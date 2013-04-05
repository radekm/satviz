-- Copyright (c) 2013 Radek Micek

module Common

infixr 1 ??, >=>

(??) : a -> (a -> b) -> b
a ?? f = f a

(>=>) : Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >=> g = \a => f a >>= g

filterM : Monad m => (a -> m Bool) -> List a -> m (List a)
filterM _ [] = return List.Nil
filterM p (x :: xs) = do
  b <- p x
  ys <- filterM p xs
  return (b ? List.(::) x ys : ys)

mapTupleM : Monad m => (a -> m b) -> (a, a) -> m (b, b)
mapTupleM f (x, y) = do
  x' <- f x
  y' <- f y
  return (x', y')

mapM_ : Monad m => (a -> m b) -> List a -> m ()
mapM_ f = sequence_ . map f

boolToInt : Bool -> Int
boolToInt b = b ? 1 : 0
