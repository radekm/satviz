-- Copyright (c) 2013 Radek Micek

module Common

infixr 1 ??, >=>

(??) : a -> (a -> b) -> b
a ?? f = f a

(>=>) : Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >=> g = \a => f a >>= g

mapM_ : Monad m => (a -> m b) -> List a -> m ()
mapM_ f = sequence_ . map f

boolToInt : Bool -> Int
boolToInt b = b ? 1 : 0
