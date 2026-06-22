-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| A minimal JSON parser for the Trope IR subset (objects, arrays, strings,
||| non-negative integers, booleans, null). No floats or \u escapes are needed by
||| the IR. `%default covering` (a parser is not structurally total without fuel;
||| this is executable code, not a proof — no axioms or escape hatches).
module Checker.Json

import Data.String
import Data.List

%default covering

public export
data JValue : Type where
  JNull : JValue
  JBool : Bool -> JValue
  JNum  : Integer -> JValue
  JStr  : String -> JValue
  JArr  : List JValue -> JValue
  JObj  : List (String, JValue) -> JValue

isWs : Char -> Bool
isWs c = c == ' ' || c == '\n' || c == '\t' || c == '\r'

skipWs : List Char -> List Char
skipWs (c :: cs) = if isWs c then skipWs cs else c :: cs
skipWs [] = []

-- string body, after the opening quote
parseStr : List Char -> Either String (String, List Char)
parseStr = go []
  where
    go : List Char -> List Char -> Either String (String, List Char)
    go acc ('"' :: rest)        = Right (pack (reverse acc), rest)
    go acc ('\\' :: e :: rest)  =
      let c : Char = case e of
                       'n' => '\n'; 't' => '\t'; 'r' => '\r'
                       'b' => chr 8; 'f' => chr 12
                       _   => e        -- " \ / and anything else: literal
      in go (c :: acc) rest
    go acc (c :: rest)          = go (c :: acc) rest
    go _   []                   = Left "unterminated string"

isDigit' : Char -> Bool
isDigit' c = c >= '0' && c <= '9'

parseNum : List Char -> Either String (Integer, List Char)
parseNum cs =
  let (neg, rest) = case cs of ('-' :: r) => (True, r); _ => (False, cs)
      (ds, rest2) = span isDigit' rest
  in case ds of
       [] => Left "expected number"
       _  => Right (let n = cast {to=Integer} (pack ds) in if neg then negate n else n, rest2)

mutual
  parseValue : List Char -> Either String (JValue, List Char)
  parseValue cs = case skipWs cs of
    ('"' :: rest) => do (s, r) <- parseStr rest; Right (JStr s, r)
    ('{' :: rest) => parseObj (skipWs rest) []
    ('[' :: rest) => parseArr (skipWs rest) []
    ('t' :: 'r' :: 'u' :: 'e' :: rest)            => Right (JBool True, rest)
    ('f' :: 'a' :: 'l' :: 's' :: 'e' :: rest)     => Right (JBool False, rest)
    ('n' :: 'u' :: 'l' :: 'l' :: rest)            => Right (JNull, rest)
    (c :: rest) => if c == '-' || isDigit' c
                     then do (n, r) <- parseNum (c :: rest); Right (JNum n, r)
                     else Left ("unexpected character '" ++ singleton c ++ "'")
    [] => Left "unexpected end of input"

  parseArr : List Char -> List JValue -> Either String (JValue, List Char)
  parseArr (']' :: rest) acc = Right (JArr (reverse acc), rest)
  parseArr cs acc = do
    (v, r) <- parseValue cs
    case skipWs r of
      (',' :: r2) => parseArr (skipWs r2) (v :: acc)
      (']' :: r2) => Right (JArr (reverse (v :: acc)), r2)
      _           => Left "expected ',' or ']' in array"

  parseObj : List Char -> List (String, JValue) -> Either String (JValue, List Char)
  parseObj ('}' :: rest) acc = Right (JObj (reverse acc), rest)
  parseObj cs acc = case skipWs cs of
    ('"' :: rest) => do
      (k, r) <- parseStr rest
      case skipWs r of
        (':' :: r2) => do
          (v, r3) <- parseValue (skipWs r2)
          case skipWs r3 of
            (',' :: r4) => parseObj (skipWs r4) ((k, v) :: acc)
            ('}' :: r4) => Right (JObj (reverse ((k, v) :: acc)), r4)
            _           => Left "expected ',' or '}' in object"
        _ => Left "expected ':' in object"
    _ => Left "expected string key in object"

||| Parse a whole JSON document; trailing whitespace permitted.
export
parseJSON : String -> Either String JValue
parseJSON s = do
  (v, rest) <- parseValue (unpack s)
  case skipWs rest of
    [] => Right v
    _  => Left "trailing content after JSON value"

-- Small accessors used by the decoder.
export
field : String -> JValue -> Maybe JValue
field k (JObj kvs) = lookup k kvs
field _ _ = Nothing

export
asStr : JValue -> Maybe String
asStr (JStr s) = Just s
asStr _ = Nothing

export
asArr : JValue -> Maybe (List JValue)
asArr (JArr xs) = Just xs
asArr _ = Nothing
