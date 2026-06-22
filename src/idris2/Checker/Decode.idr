-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The reference validator: JValue -> Document, rejecting malformed Trope IR and
||| NAMING the offending coordinate. This is the validation boundary (HC-3): the
||| three deceptive grades (Falsified/Misbound/Conflated) and any untagged merge
||| are rejected here, and HC-4 (bond coherent with the bearer's fate) is enforced
||| so incoherent grades cannot decode.
module Checker.Decode

import Data.List
import Data.String
import Trope.Fidelity
import Trope.Coords
import Trope.Grade
import Checker.Json
import Checker.Ir

%default covering

kOf : JValue -> Maybe String
kOf v = field "k" v >>= asStr

decodeDelta : String -> JValue -> Either String Delta
decodeDelta path (JNum n) = if n < 0 then Left (path ++ ": negative delta")
                                     else Right (Q (cast n))
decodeDelta path (JStr "inf") = Right Total
decodeDelta path (JStr "top") = Right Unknown
decodeDelta path _ = Left (path ++ ": delta must be a non-negative integer or \"inf\"/\"top\"")

||| isQ = is this the quality field (Predicated allowed only there).
decodeFate : String -> Bool -> JValue -> Either String Fate
decodeFate path isQ v = case kOf v of
  Just "Present"    => Right Present
  Just "Dropped"    => Right Dropped
  Just "Attenuated" => case field "delta" v of
                         Just d  => map Atten (decodeDelta (path ++ "/delta") d)
                         Nothing => Left (path ++ ": Attenuated requires delta")
  Just "Predicated" => if isQ then Right Predicated
                              else Left (path ++ ": Predicated is well-formed only on the quality field")
  Just "Falsified"  => Left (path ++ ": deceptive Falsified is not writable (prevent profile)")
  Just other        => Left (path ++ ": unknown fate \"" ++ other ++ "\"")
  Nothing           => Left (path ++ ": fate missing \"k\"")

decodeBond : String -> JValue -> Either String Bond
decodeBond path v = case kOf v of
  Just "Intact"   => Right Intact
  Just "Withheld" => Right Withheld
  Just "Severed"  => Right Severed
  Just "Misbound" => Left (path ++ ": deceptive Misbound is not writable (prevent profile)")
  Just other      => Left (path ++ ": unknown bond \"" ++ other ++ "\"")
  Nothing         => Left (path ++ ": bond missing \"k\"")

decodeMerge : String -> JValue -> Either String Merge
decodeMerge path v = case kOf v of
  Just "Single"    => Right Single
  Just "Fused"     => case field "tau" v >>= asStr of
                        Just t  => if t == "" then Left (path ++ ": Fused tag must be non-empty")
                                              else Right Fused
                        Nothing => Left (path ++ ": Fused requires a provenance tag (untagged merge)")
  Just "Conflated" => Left (path ++ ": deceptive Conflated is not writable (untagged merge)")
  Just other       => Left (path ++ ": unknown merge \"" ++ other ++ "\"")
  Nothing          => Left (path ++ ": merge missing \"k\"")

bearerAbsent : Fate -> Bool
bearerAbsent Dropped = True
bearerAbsent _       = False

reqField : String -> String -> JValue -> Either String JValue
reqField path k v = maybe (Left (path ++ ": missing \"" ++ k ++ "\"")) Right (field k v)

decodeGrade : String -> JValue -> Either String Grade
decodeGrade ePath v = do
  fa <- reqField (ePath ++ "/grade") "fate" v
  q  <- reqField (ePath ++ "/grade/fate") "quality" fa >>= decodeFate (ePath ++ "/grade/fate/quality") True
  b  <- reqField (ePath ++ "/grade/fate") "bearer"  fa >>= decodeFate (ePath ++ "/grade/fate/bearer") False
  c  <- reqField (ePath ++ "/grade/fate") "context" fa >>= decodeFate (ePath ++ "/grade/fate/context") False
  r  <- reqField (ePath ++ "/grade/fate") "record"  fa >>= decodeFate (ePath ++ "/grade/fate/record") False
  bo <- reqField (ePath ++ "/grade") "bond"  v >>= decodeBond  (ePath ++ "/grade/bond")
  me <- reqField (ePath ++ "/grade") "merge" v >>= decodeMerge (ePath ++ "/grade/merge")
  -- HC-4: bond coherent with bearer presence.
  let coherent = if bearerAbsent b
                   then (case bo of Intact => False; _ => True)     -- absent: Withheld/Severed only
                   else (case bo of Intact => True;  _ => False)    -- present: Intact only
  if coherent then Right (MkGrade q b c r bo me)
              else Left (ePath ++ "/grade/bond: incoherent with the bearer's fate (HC-4)")

decodeNodeType : String -> Either String NodeType
decodeNodeType "Trope"           = Right NTrope
decodeNodeType "FloatingQuality" = Right NFloating
decodeNodeType "Codomain"        = Right NCodomain
decodeNodeType o = Left ("nodes: unknown type \"" ++ o ++ "\"")

strList : List JValue -> List String
strList xs = mapMaybe asStr xs

decodeNode : JValue -> Either String Node
decodeNode v = do
  i  <- maybe (Left "nodes: missing id") Right (field "id" v >>= asStr)
  ts <- maybe (Left ("nodes/" ++ i ++ ": missing type")) Right (field "type" v >>= asStr)
  ty <- decodeNodeType ts
  let pres = maybe [] strList (field "present" v >>= asArr)
  -- FloatingQuality must not list a bearer field.
  case ty of
    NFloating => if elem "bearer" pres
                   then Left ("nodes/" ++ i ++ "/present: FloatingQuality may not list a bearer")
                   else Right (MkNode i ty pres)
    _ => Right (MkNode i ty pres)

decodeEdge : JValue -> Either String Edge
decodeEdge v = do
  i  <- maybe (Left "edges: missing id") Right (field "id" v >>= asStr)
  ef <- maybe (Left ("edges/" ++ i ++ ": missing effect")) Right (field "effect" v >>= asStr)
  let ins = maybe [] strList (field "inputs" v >>= asArr)
  ou <- maybe (Left ("edges/" ++ i ++ ": missing output")) Right (field "output" v >>= asStr)
  g  <- maybe (Left ("edges/" ++ i ++ ": missing grade")) Right (field "grade" v)
        >>= decodeGrade ("edges/" ++ i)
  Right (MkEdge i ef ins ou g)

floorFate : Maybe JValue -> String -> Either String (Maybe Fate)
floorFate Nothing  _ = Right Nothing
floorFate (Just o) k = case field k o of
  Just fv => map Just (decodeFate ("use_model/floor/fate/" ++ k) (k == "quality") fv)
  Nothing => Right Nothing

floorBond : JValue -> Either String (Maybe Bond)
floorBond v = case field "bond" v of
  Just bv => map Just (decodeBond "use_model/floor/bond" bv)
  Nothing => Right Nothing

floorMerge : JValue -> Either String (Maybe Merge)
floorMerge v = case field "merge" v of
  Just mv => map Just (decodeMerge "use_model/floor/merge" mv)
  Nothing => Right Nothing

decodeFloor : JValue -> Either String Floor
decodeFloor v = do
  let fa = field "fate" v
  q <- floorFate fa "quality"
  b <- floorFate fa "bearer"
  c <- floorFate fa "context"
  r <- floorFate fa "record"
  bo <- floorBond v
  me <- floorMerge v
  Right (MkFloor q b c r bo me)

mapM' : (a -> Either String b) -> List a -> Either String (List b)
mapM' f [] = Right []
mapM' f (x :: xs) = do y <- f x; ys <- mapM' f xs; Right (y :: ys)

export
decodeDoc : JValue -> Either String Document
decodeDoc v = do
  ns <- maybe (Left "missing nodes") Right (field "nodes" v >>= asArr) >>= mapM' decodeNode
  es <- maybe (Left "missing edges") Right (field "edges" v >>= asArr) >>= mapM' decodeEdge
  um <- maybe (Left "missing use_model") Right (field "use_model" v)
  ou <- maybe (Left "use_model: missing output") Right (field "output" um >>= asStr)
  fl <- maybe (Left "use_model: missing floor") Right (field "floor" um) >>= decodeFloor
  Right (MkDocument ns es ou fl)
