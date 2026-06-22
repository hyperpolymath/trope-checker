-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| In-memory Trope IR (nodes, edges, partial floor), built on the verified core's
||| grade types (package `trope`). The JSON wire format is in schemas/; the decoder
||| (Trope.Decode) is the reference validator that rejects malformed IR.
module Checker.Ir

import Trope.Fidelity
import Trope.Coords
import Trope.Grade

%default total

public export
data NodeType = NTrope | NFloating | NCodomain

public export
record Node where
  constructor MkNode
  nid     : String
  ntype   : NodeType
  present : List String

public export
record Edge where
  constructor MkEdge
  eid    : String
  effect : String
  inputs : List String
  output : String
  egrade : Grade

||| A partial floor: each coordinate is optional; an absent coordinate imposes no
||| demand (calculus §5).
public export
record Floor where
  constructor MkFloor
  fQ     : Maybe Fate
  fB     : Maybe Fate
  fC     : Maybe Fate
  fR     : Maybe Fate
  fBond  : Maybe Bond
  fMerge : Maybe Merge

public export
record Document where
  constructor MkDocument
  nodes   : List Node
  edges   : List Edge
  outNode : String
  floor   : Floor
