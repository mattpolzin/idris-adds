module Data.String.NonEmptyString

import Data.List

export
data NonEmptyString: Type where
  Just: Char -> String -> NonEmptyString

export
Show NonEmptyString where
  show (Just e es) = e `strCons` es

export
nonEmpty : String -> Maybe NonEmptyString
nonEmpty str with (unpack str)
  nonEmpty _ | [] = Nothing
  nonEmpty _ | (x :: xs) = Just (Just x (pack xs))

export
fromString : (str : String) -> {auto prf : NonEmpty (unpack str)} -> NonEmptyString
fromString str with (unpack str)
  fromString str | [] = absurd prf
  fromString str | (x :: xs) = Just x (pack xs)
  

testFromString : NonEmptyString
testFromString = "Hello"

-- testFromString' : NonEmptyString
-- testFromString' = ""
