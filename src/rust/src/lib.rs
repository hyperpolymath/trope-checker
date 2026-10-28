// SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//
// Rust fast-core tropechecker LIBRARY: the grade algebra, decoder, and verdict
// procedure. A SECOND
// implementation, validated against the Idris2 reference via the conformance corpus.
// Dependency-free (std only). Mirrors the calculus grade algebra (spec/calculus.adoc)
// and the prevent profile (HC-3/HC-4). Exit codes: 0 sufficient, 1 insufficient,
// 2 validation-fault, 3 io, 64 usage.

#![allow(dead_code)]

use std::collections::BTreeMap;

// ──────────────────────────── JSON (minimal, std-only) ────────────────────────────
#[derive(Clone, Debug)]
pub enum Json {
    Null,
    Bool(bool),
    Num(i64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

pub struct P<'a> {
    s: &'a [u8],
    i: usize,
}
impl<'a> P<'a> {
    #[must_use]
    pub fn new(s: &'a str) -> Self {
        P {
            s: s.as_bytes(),
            i: 0,
        }
    }
    pub fn ws(&mut self) {
        while self.i < self.s.len() && matches!(self.s[self.i], b' ' | b'\n' | b'\t' | b'\r') {
            self.i += 1;
        }
    }
    /// Parse the next JSON value.
    ///
    /// # Errors
    /// Returns an error for a missing or malformed value.
    pub fn value(&mut self) -> Result<Json, String> {
        self.ws();
        if self.i >= self.s.len() {
            return Err("unexpected end of input".into());
        }
        match self.s[self.i] {
            b'"' => self.string().map(Json::Str),
            b'{' => self.object(),
            b'[' => self.array(),
            b't' => {
                self.lit("true")?;
                Ok(Json::Bool(true))
            }
            b'f' => {
                self.lit("false")?;
                Ok(Json::Bool(false))
            }
            b'n' => {
                self.lit("null")?;
                Ok(Json::Null)
            }
            c if c == b'-' || c.is_ascii_digit() => self.number(),
            c => Err(format!("unexpected character '{}'", c as char)),
        }
    }
    /// Consume the expected literal.
    ///
    /// # Errors
    /// Returns an error if the remaining input does not begin with `w`.
    pub fn lit(&mut self, w: &str) -> Result<(), String> {
        if self.s[self.i..].starts_with(w.as_bytes()) {
            self.i += w.len();
            Ok(())
        } else {
            Err(format!("expected '{w}'"))
        }
    }
    /// Parse a string after its opening quote.
    ///
    /// # Errors
    /// Returns an error if the string is unterminated.
    pub fn string(&mut self) -> Result<String, String> {
        self.i += 1; // opening quote
        let mut out = String::new();
        while self.i < self.s.len() {
            let c = self.s[self.i];
            self.i += 1;
            match c {
                b'"' => return Ok(out),
                b'\\' => {
                    if self.i >= self.s.len() {
                        break;
                    }
                    let e = self.s[self.i];
                    self.i += 1;
                    out.push(match e {
                        b'n' => '\n',
                        b't' => '\t',
                        b'r' => '\r',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        _ => e as char,
                    });
                }
                _ => {
                    // pass UTF-8 bytes through: collect this byte and any continuation bytes
                    let start = self.i - 1;
                    while self.i < self.s.len() && self.s[self.i] & 0xC0 == 0x80 {
                        self.i += 1;
                    }
                    out.push_str(std::str::from_utf8(&self.s[start..self.i]).unwrap_or("?"));
                }
            }
        }
        Err("unterminated string".into())
    }
    /// Parse an integer at the current position.
    ///
    /// # Errors
    /// Returns an error for invalid integers or values outside the `i64` range.
    pub fn number(&mut self) -> Result<Json, String> {
        let start = self.i;
        if self.s[self.i] == b'-' {
            self.i += 1;
        }
        while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
            self.i += 1;
        }
        // The slice can only contain b'-' and ASCII digits (that is the loop
        // invariant above), so it is always valid UTF-8 and this decode cannot
        // actually fail. It is still written as a recoverable error rather than
        // a panicking unwrap: the safety argument lives in a loop three lines
        // up, a later edit to the scanning conditions could invalidate it
        // silently, and a validation fault (exit 2) is the documented contract
        // for malformed input — a panic is not. Behaviour on every reachable
        // input is unchanged.
        std::str::from_utf8(&self.s[start..self.i])
            .map_err(|_| "bad number: not valid UTF-8".to_string())?
            .parse::<i64>()
            .map(Json::Num)
            .map_err(|_| "bad number".into())
    }
    /// Parse an array after its opening bracket.
    ///
    /// # Errors
    /// Returns an error for malformed elements or missing delimiters.
    pub fn array(&mut self) -> Result<Json, String> {
        self.i += 1;
        let mut v = Vec::new();
        self.ws();
        if self.i < self.s.len() && self.s[self.i] == b']' {
            self.i += 1;
            return Ok(Json::Arr(v));
        }
        loop {
            v.push(self.value()?);
            self.ws();
            match self.s.get(self.i) {
                Some(b',') => {
                    self.i += 1;
                }
                Some(b']') => {
                    self.i += 1;
                    return Ok(Json::Arr(v));
                }
                _ => return Err("expected ',' or ']' in array".into()),
            }
        }
    }
    /// Parse an object after its opening brace.
    ///
    /// # Errors
    /// Returns an error for malformed keys, values, or delimiters.
    pub fn object(&mut self) -> Result<Json, String> {
        self.i += 1;
        let mut v = Vec::new();
        self.ws();
        if self.i < self.s.len() && self.s[self.i] == b'}' {
            self.i += 1;
            return Ok(Json::Obj(v));
        }
        loop {
            self.ws();
            if self.s.get(self.i) != Some(&b'"') {
                return Err("expected string key".into());
            }
            let k = self.string()?;
            self.ws();
            if self.s.get(self.i) != Some(&b':') {
                return Err("expected ':'".into());
            }
            self.i += 1;
            let val = self.value()?;
            v.push((k, val));
            self.ws();
            match self.s.get(self.i) {
                Some(b',') => {
                    self.i += 1;
                }
                Some(b'}') => {
                    self.i += 1;
                    return Ok(Json::Obj(v));
                }
                _ => return Err("expected ',' or '}' in object".into()),
            }
        }
    }
}
/// Parse one complete JSON value.
///
/// # Errors
/// Returns an error for malformed input or trailing content.
pub fn parse_json(s: &str) -> Result<Json, String> {
    let mut p = P::new(s);
    let v = p.value()?;
    p.ws();
    if p.i != p.s.len() {
        return Err("trailing content after JSON value".into());
    }
    Ok(v)
}
impl Json {
    #[must_use]
    pub fn field(&self, k: &str) -> Option<&Json> {
        if let Json::Obj(kvs) = self {
            kvs.iter().find(|(kk, _)| kk == k).map(|(_, v)| v)
        } else {
            None
        }
    }
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        if let Json::Str(s) = self {
            Some(s)
        } else {
            None
        }
    }
    #[must_use]
    pub fn as_arr(&self) -> Option<&Vec<Json>> {
        if let Json::Arr(a) = self {
            Some(a)
        } else {
            None
        }
    }
}

// ──────────────────────────── grade algebra (mirror) ────────────────────────────
#[derive(Clone, PartialEq)]
pub enum Delta {
    Q(i64),
    Inf,
    Top,
}
#[derive(Clone, PartialEq)]
pub enum Fate {
    Present,
    Atten(Delta),
    Predicated,
    Dropped,
    Falsified,
}
#[derive(Clone, PartialEq)]
pub enum Bond {
    Intact,
    Withheld,
    Severed,
    Misbound,
}
#[derive(Clone, PartialEq)]
pub enum Merge {
    Single,
    Fused,
    Conflated,
}

// loss magnitude key: bigger = more loss = less retention
#[must_use]
pub fn dkey(d: &Delta) -> (u8, i64) {
    match d {
        Delta::Q(n) => (0, *n),
        Delta::Inf => (1, 0),
        Delta::Top => (2, 0),
    }
}
#[must_use]
pub fn dadd(a: &Delta, b: &Delta) -> Delta {
    match (a, b) {
        (Delta::Top, _) | (_, Delta::Top) => Delta::Top,
        (Delta::Inf, _) | (_, Delta::Inf) => Delta::Inf,
        (Delta::Q(x), Delta::Q(y)) => Delta::Q(x + y),
    }
}
// fate retention order: x ⊑ y (y retains at least as much as x).
// R-2026-07-07 (A2): a CHAIN — Falsified ⊏ Dropped ⊏ Predicated ⊏ Atten δ ⊏ Present
// (Dropped ⊑ Predicated now true; the converse stays false).
/// Return whether `hi` retains at least as much as `lo`.
///
/// Honest fates ascend from `Dropped` through `Predicated` and attenuation to
/// `Present`; smaller attenuation retains more. `Falsified` compares only with itself.
#[must_use]
pub fn fate_le(lo: &Fate, hi: &Fate) -> bool {
    use Fate::{Atten, Dropped, Falsified, Predicated, Present};
    if lo == hi {
        return true;
    }
    if matches!(lo, Falsified) || matches!(hi, Falsified) {
        return false;
    }
    if matches!(hi, Present) {
        return true;
    }
    if matches!(lo, Present) {
        return false;
    }
    match (lo, hi) {
        (Atten(a), Atten(b)) => dkey(a) >= dkey(b),
        // R-2026-07-07 (A2): a checkbox ⊒ nothing.
        (Predicated | Dropped, Atten(_)) | (Dropped, Predicated) => true,
        _ => false,
    }
}
/// Compose two fates, adding attenuation losses.
///
/// `Present` is the identity; `Falsified` absorbs either operand, followed by
/// `Dropped` and then `Predicated`. For attenuation, `Top` absorbs `Inf`, which
/// absorbs finite losses. Zero attenuation is not normalised here.
///
/// # Panics
/// Panics if finite loss addition overflows with overflow checks enabled.
#[must_use]
pub fn fate_compose(a: &Fate, b: &Fate) -> Fate {
    use Fate::{Atten, Dropped, Falsified, Predicated, Present};
    match (a, b) {
        // R-2026-07-07 (A1): the lie survives the drop.
        (Falsified, _) | (Dropped | Atten(_) | Predicated, Falsified) => Falsified,
        (Dropped, _) | (Atten(_) | Predicated, Dropped) => Dropped,
        (Present, f) => f.clone(),
        (Atten(d1), Present) => Atten(d1.clone()),
        (Atten(d1), Atten(d2)) => Atten(dadd(d1, d2)),
        (Atten(_), Predicated) | (Predicated, _) => Predicated,
    }
}
#[must_use]
pub fn fate_meet(a: &Fate, b: &Fate) -> Fate {
    if fate_le(a, b) {
        a.clone()
    } else if fate_le(b, a) {
        b.clone()
    } else {
        Fate::Dropped
    }
}
#[must_use]
pub fn bond_rank(b: &Bond) -> i8 {
    match b {
        Bond::Intact => 3,
        Bond::Withheld => 2,
        Bond::Severed => 1,
        Bond::Misbound => 0,
    }
}
#[must_use]
pub fn bond_le(lo: &Bond, hi: &Bond) -> bool {
    if matches!(lo, Bond::Misbound) || matches!(hi, Bond::Misbound) {
        return lo == hi;
    }
    bond_rank(lo) <= bond_rank(hi)
}
#[must_use]
pub fn bond_compose(a: &Bond, b: &Bond) -> Bond {
    if matches!(a, Bond::Misbound) || matches!(b, Bond::Misbound) {
        return Bond::Misbound;
    }
    if bond_rank(a) <= bond_rank(b) {
        a.clone()
    } else {
        b.clone()
    }
}
#[must_use]
pub fn bond_meet(a: &Bond, b: &Bond) -> Bond {
    bond_compose(a, b)
}
#[must_use]
pub fn merge_rank(m: &Merge) -> i8 {
    match m {
        Merge::Single => 3,
        Merge::Fused => 2,
        Merge::Conflated => 1,
    }
}
#[must_use]
pub fn merge_le(lo: &Merge, hi: &Merge) -> bool {
    if matches!(lo, Merge::Conflated) || matches!(hi, Merge::Conflated) {
        return lo == hi;
    }
    merge_rank(lo) <= merge_rank(hi)
}
#[must_use]
pub fn merge_compose(a: &Merge, b: &Merge) -> Merge {
    if matches!(a, Merge::Conflated) || matches!(b, Merge::Conflated) {
        return Merge::Conflated;
    }
    if merge_rank(a) <= merge_rank(b) {
        a.clone()
    } else {
        b.clone()
    }
}
#[must_use]
pub fn merge_meet(a: &Merge, b: &Merge) -> Merge {
    merge_compose(a, b)
}

#[derive(Clone)]
pub struct Grade {
    pub q: Fate,
    pub b: Fate,
    pub c: Fate,
    pub r: Fate,
    pub bond: Bond,
    pub merge: Merge,
}
#[must_use]
pub fn epsilon() -> Grade {
    Grade {
        q: Fate::Present,
        b: Fate::Present,
        c: Fate::Present,
        r: Fate::Present,
        bond: Bond::Intact,
        merge: Merge::Single,
    }
}
#[must_use]
pub fn grade_compose(a: &Grade, b: &Grade) -> Grade {
    Grade {
        q: fate_compose(&a.q, &b.q),
        b: fate_compose(&a.b, &b.b),
        c: fate_compose(&a.c, &b.c),
        r: fate_compose(&a.r, &b.r),
        bond: bond_compose(&a.bond, &b.bond),
        merge: merge_compose(&a.merge, &b.merge),
    }
}
#[must_use]
pub fn grade_meet(a: &Grade, b: &Grade) -> Grade {
    Grade {
        q: fate_meet(&a.q, &b.q),
        b: fate_meet(&a.b, &b.b),
        c: fate_meet(&a.c, &b.c),
        r: fate_meet(&a.r, &b.r),
        bond: bond_meet(&a.bond, &b.bond),
        merge: merge_meet(&a.merge, &b.merge),
    }
}

// ──────────────────────────── IR + decode (HC-3/HC-4) ────────────────────────────
pub struct Edge {
    pub id: String,
    pub inputs: Vec<String>,
    pub output: String,
    pub grade: Grade,
}
pub struct Node {
    pub id: String,
    pub kind: String,
    pub present: Vec<String>,
}
pub struct Floor {
    pub q: Option<Fate>,
    pub b: Option<Fate>,
    pub c: Option<Fate>,
    pub r: Option<Fate>,
    pub bond: Option<Bond>,
    pub merge: Option<Merge>,
}
pub struct Doc {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub out: String,
    pub floor: Floor,
}

/// Decode a fidelity delta.
///
/// # Errors
/// Returns an error unless the value is a non-negative integer, `"inf"`, or `"top"`.
pub fn dec_delta(path: &str, v: &Json) -> Result<Delta, String> {
    match v {
        Json::Num(n) if *n >= 0 => Ok(Delta::Q(*n)),
        Json::Str(s) if s == "inf" => Ok(Delta::Inf),
        Json::Str(s) if s == "top" => Ok(Delta::Top),
        _ => Err(format!(
            "{path}: delta must be a non-negative integer or \"inf\"/\"top\""
        )),
    }
}
/// Decode a fate, normalising zero attenuation to presence.
///
/// Set `is_q` for the quality coordinate, where `Predicated` is permitted.
/// `path` identifies the coordinate in errors, including propagated delta errors.
///
/// # Errors
/// Returns an error for malformed or deceptive fates, or predicates outside quality.
pub fn dec_fate(path: &str, is_q: bool, v: &Json) -> Result<Fate, String> {
    match v.field("k").and_then(|k| k.as_str()) {
        Some("Present") => Ok(Fate::Present),
        Some("Dropped") => Ok(Fate::Dropped),
        // R-2026-07-07-03 (A3, ADR 0004): `Attenuated(0) = Present` is imposed by
        // NORMALIZATION AT IR INGEST — Atten(Q 0) is rewritten to Present here,
        // before any grading. Composition preserves normal forms (finite tropical
        // addition reaches 0 only from 0 + 0), so the algebra mirror is untouched.
        Some("Attenuated") => match v.field("delta") {
            Some(d) => Ok(match dec_delta(&format!("{path}/delta"), d)? {
                Delta::Q(0) => Fate::Present,
                dl => Fate::Atten(dl),
            }),
            None => Err(format!("{path}: Attenuated requires delta")),
        },
        Some("Predicated") => {
            if is_q {
                Ok(Fate::Predicated)
            } else {
                Err(format!(
                    "{path}: Predicated is well-formed only on the quality field"
                ))
            }
        }
        Some("Falsified") => Err(format!(
            "{path}: deceptive Falsified is not writable (prevent profile)"
        )),
        Some(o) => Err(format!("{path}: unknown fate \"{o}\"")),
        None => Err(format!("{path}: fate missing \"k\"")),
    }
}
/// Decode a bond in the prevent profile.
///
/// # Errors
/// Returns an error for a missing, unknown, or deceptive bond.
pub fn dec_bond(path: &str, v: &Json) -> Result<Bond, String> {
    match v.field("k").and_then(|k| k.as_str()) {
        Some("Intact") => Ok(Bond::Intact),
        Some("Withheld") => Ok(Bond::Withheld),
        Some("Severed") => Ok(Bond::Severed),
        Some("Misbound") => Err(format!(
            "{path}: deceptive Misbound is not writable (prevent profile)"
        )),
        Some(o) => Err(format!("{path}: unknown bond \"{o}\"")),
        None => Err(format!("{path}: bond missing \"k\"")),
    }
}
/// Decode a merge in the prevent profile.
///
/// `Fused` requires a non-empty `tau` string; the returned merge discards the tag.
///
/// # Errors
/// Returns an error for a missing, unknown, or deceptive merge, or a missing or empty fusion tag.
pub fn dec_merge(path: &str, v: &Json) -> Result<Merge, String> {
    match v.field("k").and_then(|k| k.as_str()) {
        Some("Single") => Ok(Merge::Single),
        Some("Fused") => match v.field("tau").and_then(|t| t.as_str()) {
            Some(t) if !t.is_empty() => Ok(Merge::Fused),
            Some(_) => Err(format!("{path}: Fused tag must be non-empty")),
            None => Err(format!(
                "{path}: Fused requires a provenance tag (untagged merge)"
            )),
        },
        Some("Conflated") => Err(format!(
            "{path}: deceptive Conflated is not writable (untagged merge)"
        )),
        Some(o) => Err(format!("{path}: unknown merge \"{o}\"")),
        None => Err(format!("{path}: merge missing \"k\"")),
    }
}
/// Look up a required JSON object field.
///
/// # Errors
/// Returns an error naming the path and key when the field is absent.
pub fn req<'a>(path: &str, k: &str, v: &'a Json) -> Result<&'a Json, String> {
    v.field(k).ok_or_else(|| format!("{path}: missing \"{k}\""))
}
/// Decode a grade and check bearer/bond coherence.
///
/// `value` is the grade object; `epath` names its enclosing edge in errors.
/// After normalisation, a dropped bearer requires `Withheld` or `Severed`;
/// every other accepted bearer fate requires `Intact`.
///
/// # Errors
/// Returns an error for missing or invalid coordinates or an incoherent bond.
pub fn dec_grade(epath: &str, value: &Json) -> Result<Grade, String> {
    let fate = req(&format!("{epath}/grade"), "fate", value)?;
    let quality = dec_fate(
        &format!("{epath}/grade/fate/quality"),
        true,
        req(&format!("{epath}/grade/fate"), "quality", fate)?,
    )?;
    let bearer = dec_fate(
        &format!("{epath}/grade/fate/bearer"),
        false,
        req(&format!("{epath}/grade/fate"), "bearer", fate)?,
    )?;
    let context = dec_fate(
        &format!("{epath}/grade/fate/context"),
        false,
        req(&format!("{epath}/grade/fate"), "context", fate)?,
    )?;
    let record = dec_fate(
        &format!("{epath}/grade/fate/record"),
        false,
        req(&format!("{epath}/grade/fate"), "record", fate)?,
    )?;
    let bond = dec_bond(
        &format!("{epath}/grade/bond"),
        req(&format!("{epath}/grade"), "bond", value)?,
    )?;
    let merge = dec_merge(
        &format!("{epath}/grade/merge"),
        req(&format!("{epath}/grade"), "merge", value)?,
    )?;
    let bearer_absent = bearer == Fate::Dropped;
    let coherent = if bearer_absent {
        bond != Bond::Intact
    } else {
        bond == Bond::Intact
    };
    if !coherent {
        return Err(format!(
            "{epath}/grade/bond: incoherent with the bearer's fate (HC-4)"
        ));
    }
    Ok(Grade {
        q: quality,
        b: bearer,
        c: context,
        r: record,
        bond,
        merge,
    })
}
/// Collect an array's string entries in order, ignoring other entries.
///
/// Return an empty list if `v` is not an array.
#[must_use]
pub fn str_list(v: &Json) -> Vec<String> {
    v.as_arr().map_or_default(|a| {
        a.iter()
            .filter_map(|x| x.as_str().map(String::from))
            .collect()
    })
}
/// Decode an IR node.
///
/// Missing or non-array `present` fields become empty lists; non-string entries
/// are ignored.
///
/// # Errors
/// Returns an error for a missing or non-string ID or type, an unknown type,
/// or a `FloatingQuality` node listing `bearer` in `present`.
pub fn dec_node(v: &Json) -> Result<Node, String> {
    let id = v
        .field("id")
        .and_then(|x| x.as_str())
        .ok_or("nodes: missing id")?
        .to_string();
    let kind = v
        .field("type")
        .and_then(|x| x.as_str())
        .ok_or_else(|| format!("nodes/{id}: missing type"))?
        .to_string();
    let present = v.field("present").map_or_default(str_list);
    if kind == "FloatingQuality" && present.iter().any(|p| p == "bearer") {
        return Err(format!(
            "nodes/{id}/present: FloatingQuality may not list a bearer"
        ));
    }
    if !matches!(kind.as_str(), "Trope" | "FloatingQuality" | "Codomain") {
        return Err(format!("nodes/{id}: unknown type \"{kind}\""));
    }
    Ok(Node { id, kind, present })
}
/// Decode an IR edge.
///
/// Missing or non-array `inputs` fields become empty lists; non-string entries
/// are ignored. Grade decoding errors are propagated.
///
/// # Errors
/// Returns an error for a missing ID or output, or a missing or invalid grade.
pub fn dec_edge(v: &Json) -> Result<Edge, String> {
    let id = v
        .field("id")
        .and_then(|x| x.as_str())
        .ok_or("edges: missing id")?
        .to_string();
    let inputs = v.field("inputs").map_or_default(str_list);
    let output = v
        .field("output")
        .and_then(|x| x.as_str())
        .ok_or_else(|| format!("edges/{id}: missing output"))?
        .to_string();
    let grade = dec_grade(
        &format!("edges/{id}"),
        req(&format!("edges/{id}"), "grade", v)?,
    )?;
    Ok(Edge {
        id,
        inputs,
        output,
        grade,
    })
}
/// Decode the optional coordinates of a use-model floor.
///
/// Missing coordinates remain `None` and impose no requirement when checked.
/// Fate coordinates use the same zero-attenuation normalisation as edge grades.
///
/// # Errors
/// Returns an error if a supplied coordinate is invalid in the prevent profile.
pub fn dec_floor(v: &Json) -> Result<Floor, String> {
    let ff = |k: &str, is_q: bool| -> Result<Option<Fate>, String> {
        match v.field("fate").and_then(|fa| fa.field(k)) {
            Some(fv) => Ok(Some(dec_fate(
                &format!("use_model/floor/fate/{k}"),
                is_q,
                fv,
            )?)),
            None => Ok(None),
        }
    };
    let bo = match v.field("bond") {
        Some(bv) => Some(dec_bond("use_model/floor/bond", bv)?),
        None => None,
    };
    let me = match v.field("merge") {
        Some(mv) => Some(dec_merge("use_model/floor/merge", mv)?),
        None => None,
    };
    Ok(Floor {
        q: ff("quality", true)?,
        b: ff("bearer", false)?,
        c: ff("context", false)?,
        r: ff("record", false)?,
        bond: bo,
        merge: me,
    })
}
/// Decode an IR document under the shared 0.1/0.2 semantics.
///
/// # Errors
/// Returns an error for unsupported versions, missing document fields, or invalid nodes, edges, or floors.
pub fn dec_doc(v: &Json) -> Result<Doc, String> {
    // Accepted document versions (IR 0.2, R-2026-07-07). "0.1" stays accepted:
    // the wire format is identical, and 0.1 documents are normalized and graded
    // under the same (0.2) semantics.
    match v.field("version").and_then(Json::as_str) {
        Some("0.1" | "0.2") => {}
        Some(o) => return Err(format!("version: unsupported \"{o}\" (accepted: 0.1, 0.2)")),
        None => return Err("missing \"version\"".into()),
    }
    let nodes = v
        .field("nodes")
        .and_then(Json::as_arr)
        .ok_or("missing nodes")?
        .iter()
        .map(dec_node)
        .collect::<Result<Vec<_>, _>>()?;
    let edges = v
        .field("edges")
        .and_then(Json::as_arr)
        .ok_or("missing edges")?
        .iter()
        .map(dec_edge)
        .collect::<Result<Vec<_>, _>>()?;
    let um = v.field("use_model").ok_or("missing use_model")?;
    let out = um
        .field("output")
        .and_then(|x| x.as_str())
        .ok_or("use_model: missing output")?
        .to_string();
    let floor = dec_floor(um.field("floor").ok_or("use_model: missing floor")?)?;
    let _ = &nodes; // nodes are validated at decode; structural coherence already enforced
    Ok(Doc {
        nodes,
        edges,
        out,
        floor,
    })
}

// ──────────────────────────── checker (DAG accumulate + verdict + witness) ────────
pub fn acc(edges: &[Edge], node: &str, fuel: usize, memo: &mut BTreeMap<String, Grade>) -> Grade {
    if fuel == 0 {
        return epsilon();
    }
    if let Some(g) = memo.get(node) {
        return g.clone();
    }
    let prod = edges.iter().find(|e| e.output == node);
    let g = match prod {
        None => epsilon(),
        Some(e) => {
            let ins: Vec<Grade> = e
                .inputs
                .iter()
                .map(|s| acc(edges, s, fuel - 1, memo))
                .collect();
            match ins.len() {
                0 => e.grade.clone(),
                1 => grade_compose(&ins[0], &e.grade),
                _ => {
                    let mut m = ins[0].clone();
                    for x in &ins[1..] {
                        m = grade_meet(&m, x);
                    }
                    grade_compose(&m, &e.grade)
                }
            }
        }
    };
    memo.insert(node.to_string(), g.clone());
    g
}
#[must_use]
pub fn violations(fl: &Floor, g: &Grade) -> Vec<String> {
    let mut v = Vec::new();
    if let Some(d) = &fl.q {
        if !fate_le(d, &g.q) {
            v.push("fate.quality".into());
        }
    }
    if let Some(d) = &fl.b {
        if !fate_le(d, &g.b) {
            v.push("fate.bearer".into());
        }
    }
    if let Some(d) = &fl.c {
        if !fate_le(d, &g.c) {
            v.push("fate.context".into());
        }
    }
    if let Some(d) = &fl.r {
        if !fate_le(d, &g.r) {
            v.push("fate.record".into());
        }
    }
    if let Some(d) = &fl.bond {
        if !bond_le(d, &g.bond) {
            v.push("bond".into());
        }
    }
    if let Some(d) = &fl.merge {
        if !merge_le(d, &g.merge) {
            v.push("merge".into());
        }
    }
    v
}
#[must_use]
pub fn check(doc: &Doc) -> (String, Option<(String, String)>) {
    let fuel = doc.edges.len() + 1;
    let mut memo = BTreeMap::new();
    let final_g = acc(&doc.edges, &doc.out, fuel, &mut memo);
    let bad = violations(&doc.floor, &final_g);
    if bad.is_empty() {
        return ("p-sufficient".into(), None);
    }
    // witness: first edge (document order) whose output grade violates a failing coord
    for e in &doc.edges {
        let mut m2 = BTreeMap::new();
        let g = acc(&doc.edges, &e.output, fuel, &mut m2);
        let hit: Vec<String> = violations(&doc.floor, &g)
            .into_iter()
            .filter(|c| bad.contains(c))
            .collect();
        if let Some(c) = hit.first() {
            return ("p-insufficient".into(), Some((e.id.clone(), c.clone())));
        }
    }
    ("p-insufficient".into(), None)
}

/// The retention order ⊑ on grades: the componentwise product order.
///
/// True iff `hi` retains at least as much as `lo` in EVERY coordinate. This
/// mirrors `gradeLte` in `verification/proofs/idris2/Trope/Grade.idr` exactly —
/// the conjunction of the four field-fates with bond and merge — and adds no
/// new semantics: it is built only from the per-coordinate orders already used
/// by `violations`. The algebra is PROVED in Idris2, not here.
///
/// Exposed so downstream consumers (e.g. a query engine doing loss-bounded
/// traversal) can compare grades in-process instead of reimplementing the
/// order and forking the semantics.
#[must_use]
pub fn grade_le(lo: &Grade, hi: &Grade) -> bool {
    fate_le(&lo.q, &hi.q)
        && fate_le(&lo.b, &hi.b)
        && fate_le(&lo.c, &hi.c)
        && fate_le(&lo.r, &hi.r)
        && bond_le(&lo.bond, &hi.bond)
        && merge_le(&lo.merge, &hi.merge)
}

#[cfg(test)]
mod grade_le_tests {
    use super::*;

    /// ⊑ is reflexive (Trope.Grade: the product order over reflexive coordinates).
    #[test]
    fn reflexive() {
        assert!(grade_le(&epsilon(), &epsilon()));
    }

    /// ε is the TOP of the retention order: everything retains at most as much.
    #[test]
    fn epsilon_is_top() {
        let mut g = epsilon();
        g.q = Fate::Atten(Delta::Q(1));
        assert!(grade_le(&g, &epsilon()), "any loss must be <= epsilon");
        assert!(
            !grade_le(&epsilon(), &g),
            "epsilon must not be <= a lossy grade"
        );
    }

    /// Retention DECREASES as loss grows, so a bigger delta is lower in the order.
    #[test]
    fn larger_delta_retains_less() {
        let (mut lo, mut hi) = (epsilon(), epsilon());
        lo.q = Fate::Atten(Delta::Q(10));
        hi.q = Fate::Atten(Delta::Q(3));
        assert!(grade_le(&lo, &hi), "Atten(10) retains less than Atten(3)");
        assert!(!grade_le(&hi, &lo));
    }

    /// Unknown (⊤) is the BOTTOM: below every finite loss, and below Total.
    #[test]
    fn unknown_is_bottom() {
        let (mut top, mut fin) = (epsilon(), epsilon());
        top.q = Fate::Atten(Delta::Top);
        fin.q = Fate::Atten(Delta::Q(9999));
        assert!(grade_le(&top, &fin), "Top must be below any finite loss");
        assert!(!grade_le(&fin, &top));
    }

    /// The order is COMPONENTWISE: failing any one coordinate fails the whole.
    #[test]
    fn componentwise() {
        let mut g = epsilon();
        g.bond = Bond::Severed;
        assert!(
            !grade_le(&epsilon(), &g),
            "a severed bond must break the order"
        );
        let mut h = epsilon();
        h.r = Fate::Dropped;
        assert!(
            !grade_le(&epsilon(), &h),
            "a dropped record must break the order"
        );
    }

    /// The pair a downstream query engine depends on: the same declared loss
    /// satisfies one floor and not another. This is the whole use-relativity claim.
    #[test]
    fn same_loss_different_floors() {
        let mut residue = epsilon();
        residue.q = Fate::Atten(Delta::Q(6));
        let (mut strict, mut loose) = (epsilon(), epsilon());
        strict.q = Fate::Atten(Delta::Q(3));
        loose.q = Fate::Atten(Delta::Q(10));
        assert!(
            !grade_le(&strict, &residue),
            "floor 3 must NOT be met by loss 6"
        );
        assert!(grade_le(&loose, &residue), "floor 10 must be met by loss 6");
    }
}
