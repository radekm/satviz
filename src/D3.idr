-- Copyright (c) 2013 Radek Micek

module D3

import Common

-- ---------------------------------------------------------------------------

decodeEntities : String -> IO String
decodeEntities str = mkForeign (FFun "decodeEntities" [FString] FString) str

-- ---------------------------------------------------------------------------
-- Dialogs

prompt : String -> IO (Maybe String)
prompt msg =
  mkForeign
    (FFun
       "promptHelper"
       [FString, FAny (() -> Maybe String), FAny (String -> Maybe String)]
       (FAny $ Maybe String))
    msg
    mkNothing
    mkJust
  where
    mkNothing : () -> Maybe String
    mkNothing () = Nothing
    mkJust : String -> Maybe String
    mkJust s = Just s

-- ---------------------------------------------------------------------------
-- Arrays

data Array a = MkArray Ptr

emptyA : () -> IO (Array a)
emptyA () = mkForeign (FFun "Array" [] (FAny $ Array _))

pushA : Array a -> a -> IO ()
pushA xs x = mkForeign (FFun ".push" [FAny $ Array _, FAny _] FUnit) xs x

lengthA : Array a -> IO Int
lengthA xs = mkForeign (FFun ".length" [FAny $ Array _] FInt) xs

mkArray : List a -> IO (Array a)
mkArray xs = do
  ys <- emptyA ()
  mapM_ (pushA ys) xs
  return ys

getNth : Array a -> Int -> IO a
getNth xs i = mkForeign (FFun "getNth" [FAny $ Array _, FInt] (FAny _)) xs i

setNth : Array a -> Int -> a -> IO ()
setNth xs i x =
  mkForeign (FFun "setNth" [FAny $ Array _, FInt, FAny _] FUnit) xs i x

arrayToList : {a : _} -> Array a -> IO (List a)
arrayToList {a} xs = lengthA xs >>= loop [] . flip (-) 1
  where
    loop : List a -> Int -> IO (List a)
    loop acc i =
      if i >= 0 then do
        x <- getNth xs i
        loop (x :: acc) (i - 1)
      else
        return acc

anyA : {a : _} -> (a -> Bool) -> Array a -> IO Bool
anyA {a} f xs =
  pure (/= 0) <$> mkForeign (FFun "anyA" [FAny _, FAny $ Array _] FInt) f2 xs
  where
    f2 : a -> Int
    f2 x = (f x) ? 1 : 0

filterA : {a : _} -> (a -> Bool) -> Array a -> IO (Array a)
filterA {a} f xs =
  mkForeign (FFun "filterA" [FAny _, FAny $ Array _] (FAny $ Array _)) f2 xs
  where
    f2 : a -> Int
    f2 x = (f x) ? 1 : 0

-- ---------------------------------------------------------------------------
-- Selecting elements

data Sel a b = MkSel Ptr

data NoData = MkNoData Ptr

d3 : Sel NoData NoData
d3 = unsafePerformIO
       $ mkForeign (FFun "d3Root" [] (FAny $ Sel NoData NoData))

select : String -> Sel a b -> IO (Sel a b)
select s sel =
  mkForeign (FFun ".select" [FAny $ Sel _ _, FString] (FAny $ Sel _ _)) sel s

selectAll : String -> Sel a b -> IO (Sel b NoData)
selectAll s sel =
  mkForeign
    (FFun ".selectAll" [FAny $ Sel _ _, FString] (FAny $ Sel _ _))
    sel s

-- ---------------------------------------------------------------------------
-- Operating on selections: Content

attr : String -> String -> Sel a b -> IO (Sel a b)
attr attr val sel =
  mkForeign
    (FFun ".attr" [FAny $ Sel _ _, FString, FString] (FAny $ Sel _ _))
    sel attr val

attr' : String -> (b -> Int -> IO String) -> Sel a b -> IO (Sel a b)
attr' attr f sel =
  mkForeign
    (FFun "attrPrime" [FAny $ Sel _ _, FString, FAny _] (FAny $ Sel _ _))
    sel attr f

classed : String -> Bool -> Sel a b -> IO (Sel a b)
classed cls b sel =
  mkForeign
    (FFun ".classed" [FAny $ Sel _ _, FString, FInt] (FAny $ Sel _ _))
    sel cls (b ? 1 : 0)

classed' :
  {b : _} ->
  String ->
  (b -> Int -> IO Bool) ->
  Sel a b ->
  IO (Sel a b)
classed' {b} cls f sel =
  mkForeign
    (FFun "classedPrime" [FAny $ Sel _ _, FString, FAny _] (FAny $ Sel _ _))
    sel cls f2
  where
    f2 : b -> Int -> IO Int
    f2 d i = do
      result <- f d i
      return (result ? 1 : 0)

style : String -> String -> Sel a b -> IO (Sel a b)
style name val sel =
  mkForeign
    (FFun ".style" [FAny $ Sel _ _, FString, FString] (FAny $ Sel _ _))
    sel name val

style' : String -> (b -> Int -> IO String) -> Sel a b -> IO (Sel a b)
style' name f sel =
  mkForeign
    (FFun "stylePrime" [FAny $ Sel _ _, FString, FAny _] (FAny $ Sel _ _))
    sel name f

property : String -> String -> Sel a b -> IO (Sel a b)
property name val sel =
  mkForeign
    (FFun ".property" [FAny $ Sel _ _, FString, FString] (FAny $ Sel _ _))
    sel name val

property' : String -> (b -> Int -> IO String) -> Sel a b -> IO (Sel a b)
property' name f sel =
  mkForeign
    (FFun "propertyPrime" [FAny $ Sel _ _, FString, FAny _] (FAny $ Sel _ _))
    sel name f

text : String -> Sel a b -> IO (Sel a b)
text val sel =
  mkForeign (FFun ".text" [FAny $ Sel _ _, FString] (FAny $ Sel _ _)) sel val

text' : (b -> Int -> IO String) -> Sel a b -> IO (Sel a b)
text' f sel =
  mkForeign (FFun "textPrime" [FAny $ Sel _ _, FAny _] (FAny $ Sel _ _)) sel f

html : String -> Sel a b -> IO (Sel a b)
html val sel =
  mkForeign (FFun ".html" [FAny $ Sel _ _, FString] (FAny $ Sel _ _)) sel val

html' : (b -> Int -> IO String) -> Sel a b -> IO (Sel a b)
html' f sel =
  mkForeign (FFun "htmlPrime" [FAny $ Sel _ _, FAny _] (FAny $ Sel _ _)) sel f

append : String -> Sel a b -> IO (Sel a b)
append elem sel =
  mkForeign
    (FFun ".append" [FAny $ Sel _ _, FString] (FAny $ Sel _ _))
    sel elem

remove : Sel a b -> IO ()
remove sel = mkForeign (FFun ".remove" [FAny $ Sel _ _, FUnit] FUnit) sel ()

forgetBoundData : Sel a b -> IO (Sel NoData NoData)
forgetBoundData (MkSel s) = return $ MkSel s

castBoundData : Sel a b -> IO (Sel a c)
castBoundData (MkSel s) = return $ MkSel s

-- ---------------------------------------------------------------------------
-- Operating on selections: Data

bind : Array c -> Sel a b -> IO (Sel a c)
bind arr sel =
  mkForeign
    (FFun ".data" [FAny $ Sel _ _, FAny $ Array _] (FAny $ Sel _ _))
    sel arr

bind' : (a -> Int -> IO (Array c)) -> Sel a b -> IO (Sel a c)
bind' f sel =
  mkForeign
    (FFun
       "bindPrime"
       [FAny $ Sel _ _, FAny _]
       (FAny $ Sel _ _))
    sel f

bindK : Array c -> (c -> Int -> IO String) -> Sel a b -> IO (Sel a c)
bindK arr key sel =
  mkForeign
    (FFun "bindK" [FAny $ Sel _ _, FAny $ Array _, FAny _] (FAny $ Sel _ _))
    sel arr key

bindK' :
  (a -> Int -> IO (Array c)) ->
  (c -> Int -> IO String) ->
  Sel a b ->
  IO (Sel a c)
bindK' f key sel =
  mkForeign
    (FFun "bindKPrime" [FAny $ Sel _ _, FAny _, FAny _] (FAny $ Sel _ _))
    sel f key

enter : Sel a b -> IO (Sel a b)
enter sel =
  mkForeign (FFun ".enter" [FAny $ Sel _ _, FUnit] (FAny $ Sel _ _)) sel ()

exit : Sel a b -> IO (Sel a b)
exit sel =
  mkForeign (FFun ".exit" [FAny $ Sel _ _, FUnit] (FAny $ Sel _ _)) sel ()

-- ---------------------------------------------------------------------------
-- Events

onClick : Sel a b -> (() -> IO ()) -> IO ()
onClick sel h =
  mkForeign (FFun "onClick" [FAny $ Sel _ _, FAny (() -> IO ())] FUnit) sel h
