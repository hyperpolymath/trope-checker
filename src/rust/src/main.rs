// SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//
// Rust fast-core tropechecker: a Trope IR JSON document -> verdict. A SECOND
// implementation, validated against the Idris2 reference via the conformance corpus.
// Dependency-free (std only). Mirrors the calculus grade algebra (spec/calculus.adoc)
// and the prevent profile (HC-3/HC-4). Exit codes: 0 sufficient, 1 insufficient,
// 2 validation-fault, 3 io, 64 usage.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::process::exit;

// ──────────────────────────── JSON (minimal, std-only) ────────────────────────────
#[derive(Clone, Debug)]
enum Json {
    Null,
    Bool(bool),
    Num(i64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

struct P<'a> { s: &'a [u8], i: usize }
impl<'a> P<'a> {
    fn new(s: &'a str) -> Self { P { s: s.as_bytes(), i: 0 } }
    fn ws(&mut self) { while self.i < self.s.len() && matches!(self.s[self.i], b' ' | b'\n' | b'\t' | b'\r') { self.i += 1; } }
    fn value(&mut self) -> Result<Json, String> {
        self.ws();
        if self.i >= self.s.len() { return Err("unexpected end of input".into()); }
        match self.s[self.i] {
            b'"' => self.string().map(Json::Str),
            b'{' => self.object(),
            b'[' => self.array(),
            b't' => { self.lit("true")?; Ok(Json::Bool(true)) }
            b'f' => { self.lit("false")?; Ok(Json::Bool(false)) }
            b'n' => { self.lit("null")?; Ok(Json::Null) }
            c if c == b'-' || c.is_ascii_digit() => self.number(),
            c => Err(format!("unexpected character '{}'", c as char)),
        }
    }
    fn lit(&mut self, w: &str) -> Result<(), String> {
        if self.s[self.i..].starts_with(w.as_bytes()) { self.i += w.len(); Ok(()) }
        else { Err(format!("expected '{}'", w)) }
    }
    fn string(&mut self) -> Result<String, String> {
        self.i += 1; // opening quote
        let mut out = String::new();
        while self.i < self.s.len() {
            let c = self.s[self.i]; self.i += 1;
            match c {
                b'"' => return Ok(out),
                b'\\' => {
                    if self.i >= self.s.len() { break; }
                    let e = self.s[self.i]; self.i += 1;
                    out.push(match e { b'n' => '\n', b't' => '\t', b'r' => '\r',
                        b'b' => '\u{8}', b'f' => '\u{c}', _ => e as char });
                }
                _ => {
                    // pass UTF-8 bytes through: collect this byte and any continuation bytes
                    let start = self.i - 1;
                    while self.i < self.s.len() && self.s[self.i] & 0xC0 == 0x80 { self.i += 1; }
                    out.push_str(std::str::from_utf8(&self.s[start..self.i]).unwrap_or("?"));
                }
            }
        }
        Err("unterminated string".into())
    }
    fn number(&mut self) -> Result<Json, String> {
        let start = self.i;
        if self.s[self.i] == b'-' { self.i += 1; }
        while self.i < self.s.len() && self.s[self.i].is_ascii_digit() { self.i += 1; }
        std::str::from_utf8(&self.s[start..self.i]).unwrap().parse::<i64>()
            .map(Json::Num).map_err(|_| "bad number".into())
    }
    fn array(&mut self) -> Result<Json, String> {
        self.i += 1; let mut v = Vec::new(); self.ws();
        if self.i < self.s.len() && self.s[self.i] == b']' { self.i += 1; return Ok(Json::Arr(v)); }
        loop {
            v.push(self.value()?); self.ws();
            match self.s.get(self.i) {
                Some(b',') => { self.i += 1; }
                Some(b']') => { self.i += 1; return Ok(Json::Arr(v)); }
                _ => return Err("expected ',' or ']' in array".into()),
            }
        }
    }
    fn object(&mut self) -> Result<Json, String> {
        self.i += 1; let mut v = Vec::new(); self.ws();
        if self.i < self.s.len() && self.s[self.i] == b'}' { self.i += 1; return Ok(Json::Obj(v)); }
        loop {
            self.ws();
            if self.s.get(self.i) != Some(&b'"') { return Err("expected string key".into()); }
            let k = self.string()?; self.ws();
            if self.s.get(self.i) != Some(&b':') { return Err("expected ':'".into()); }
            self.i += 1;
            let val = self.value()?; v.push((k, val)); self.ws();
            match self.s.get(self.i) {
                Some(b',') => { self.i += 1; }
                Some(b'}') => { self.i += 1; return Ok(Json::Obj(v)); }
                _ => return Err("expected ',' or '}' in object".into()),
            }
        }
    }
}
fn parse_json(s: &str) -> Result<Json, String> {
    let mut p = P::new(s);
    let v = p.value()?; p.ws();
    if p.i != p.s.len() { return Err("trailing content after JSON value".into()); }
    Ok(v)
}
impl Json {
    fn field(&self, k: &str) -> Option<&Json> {
        if let Json::Obj(kvs) = self { kvs.iter().find(|(kk, _)| kk == k).map(|(_, v)| v) } else { None }
    }
    fn as_str(&self) -> Option<&str> { if let Json::Str(s) = self { Some(s) } else { None } }
    fn as_arr(&self) -> Option<&Vec<Json>> { if let Json::Arr(a) = self { Some(a) } else { None } }
}

// ──────────────────────────── grade algebra (mirror) ────────────────────────────
#[derive(Clone, PartialEq)]
enum Delta { Q(i64), Inf, Top }
#[derive(Clone, PartialEq)]
enum Fate { Present, Atten(Delta), Predicated, Dropped, Falsified }
#[derive(Clone, PartialEq)]
enum Bond { Intact, Withheld, Severed, Misbound }
#[derive(Clone, PartialEq)]
enum Merge { Single, Fused, Conflated }

// loss magnitude key: bigger = more loss = less retention
fn dkey(d: &Delta) -> (u8, i64) { match d { Delta::Q(n) => (0, *n), Delta::Inf => (1, 0), Delta::Top => (2, 0) } }
fn dadd(a: &Delta, b: &Delta) -> Delta {
    match (a, b) { (Delta::Top, _) | (_, Delta::Top) => Delta::Top,
        (Delta::Inf, _) | (_, Delta::Inf) => Delta::Inf, (Delta::Q(x), Delta::Q(y)) => Delta::Q(x + y) }
}
// fate retention order: x ⊑ y (y retains at least as much as x)
fn fate_le(lo: &Fate, hi: &Fate) -> bool {
    use Fate::*;
    if lo == hi { return true; }
    if matches!(lo, Falsified) || matches!(hi, Falsified) { return false; }
    if matches!(hi, Present) { return true; }
    if matches!(lo, Present) { return false; }
    match (lo, hi) {
        (Atten(a), Atten(b)) => dkey(a) >= dkey(b),
        (Predicated, Atten(_)) => true,
        (Predicated, _) => false,
        (_, Predicated) => false, // lo is Atten/Dropped here
        (Dropped, Atten(_)) => true,
        (Dropped, _) => false,
        _ => false,
    }
}
fn fate_compose(a: &Fate, b: &Fate) -> Fate {
    use Fate::*;
    match (a, b) {
        (Falsified, _) => Falsified,
        (Dropped, _) => Dropped,
        (Present, f) => f.clone(),
        (Atten(_), Falsified) => Falsified,
        (Atten(_), Dropped) => Dropped,
        (Atten(d1), Present) => Atten(d1.clone()),
        (Atten(d1), Atten(d2)) => Atten(dadd(d1, d2)),
        (Atten(_), Predicated) => Predicated,
        (Predicated, Falsified) => Falsified,
        (Predicated, Dropped) => Dropped,
        (Predicated, _) => Predicated, // Present/Atten/Predicated
    }
}
fn fate_meet(a: &Fate, b: &Fate) -> Fate {
    if fate_le(a, b) { a.clone() } else if fate_le(b, a) { b.clone() } else { Fate::Dropped }
}
fn bond_rank(b: &Bond) -> i8 { match b { Bond::Intact => 3, Bond::Withheld => 2, Bond::Severed => 1, Bond::Misbound => 0 } }
fn bond_le(lo: &Bond, hi: &Bond) -> bool {
    if matches!(lo, Bond::Misbound) || matches!(hi, Bond::Misbound) { return lo == hi; }
    bond_rank(lo) <= bond_rank(hi)
}
fn bond_compose(a: &Bond, b: &Bond) -> Bond {
    if matches!(a, Bond::Misbound) || matches!(b, Bond::Misbound) { return Bond::Misbound; }
    if bond_rank(a) <= bond_rank(b) { a.clone() } else { b.clone() }
}
fn bond_meet(a: &Bond, b: &Bond) -> Bond { bond_compose(a, b) }
fn merge_rank(m: &Merge) -> i8 { match m { Merge::Single => 3, Merge::Fused => 2, Merge::Conflated => 1 } }
fn merge_le(lo: &Merge, hi: &Merge) -> bool {
    if matches!(lo, Merge::Conflated) || matches!(hi, Merge::Conflated) { return lo == hi; }
    merge_rank(lo) <= merge_rank(hi)
}
fn merge_compose(a: &Merge, b: &Merge) -> Merge {
    if matches!(a, Merge::Conflated) || matches!(b, Merge::Conflated) { return Merge::Conflated; }
    if merge_rank(a) <= merge_rank(b) { a.clone() } else { b.clone() }
}
fn merge_meet(a: &Merge, b: &Merge) -> Merge { merge_compose(a, b) }

#[derive(Clone)]
struct Grade { q: Fate, b: Fate, c: Fate, r: Fate, bond: Bond, merge: Merge }
fn epsilon() -> Grade { Grade { q: Fate::Present, b: Fate::Present, c: Fate::Present, r: Fate::Present, bond: Bond::Intact, merge: Merge::Single } }
fn grade_compose(a: &Grade, b: &Grade) -> Grade {
    Grade { q: fate_compose(&a.q, &b.q), b: fate_compose(&a.b, &b.b), c: fate_compose(&a.c, &b.c),
        r: fate_compose(&a.r, &b.r), bond: bond_compose(&a.bond, &b.bond), merge: merge_compose(&a.merge, &b.merge) }
}
fn grade_meet(a: &Grade, b: &Grade) -> Grade {
    Grade { q: fate_meet(&a.q, &b.q), b: fate_meet(&a.b, &b.b), c: fate_meet(&a.c, &b.c),
        r: fate_meet(&a.r, &b.r), bond: bond_meet(&a.bond, &b.bond), merge: merge_meet(&a.merge, &b.merge) }
}

// ──────────────────────────── IR + decode (HC-3/HC-4) ────────────────────────────
struct Edge { id: String, inputs: Vec<String>, output: String, grade: Grade }
struct Node { id: String, kind: String, present: Vec<String> }
struct Floor { q: Option<Fate>, b: Option<Fate>, c: Option<Fate>, r: Option<Fate>, bond: Option<Bond>, merge: Option<Merge> }
struct Doc { nodes: Vec<Node>, edges: Vec<Edge>, out: String, floor: Floor }

fn dec_delta(path: &str, v: &Json) -> Result<Delta, String> {
    match v {
        Json::Num(n) if *n >= 0 => Ok(Delta::Q(*n)),
        Json::Str(s) if s == "inf" => Ok(Delta::Inf),
        Json::Str(s) if s == "top" => Ok(Delta::Top),
        _ => Err(format!("{}: delta must be a non-negative integer or \"inf\"/\"top\"", path)),
    }
}
fn dec_fate(path: &str, is_q: bool, v: &Json) -> Result<Fate, String> {
    match v.field("k").and_then(|k| k.as_str()) {
        Some("Present") => Ok(Fate::Present),
        Some("Dropped") => Ok(Fate::Dropped),
        Some("Attenuated") => match v.field("delta") {
            Some(d) => Ok(Fate::Atten(dec_delta(&format!("{}/delta", path), d)?)),
            None => Err(format!("{}: Attenuated requires delta", path)),
        },
        Some("Predicated") => if is_q { Ok(Fate::Predicated) }
            else { Err(format!("{}: Predicated is well-formed only on the quality field", path)) },
        Some("Falsified") => Err(format!("{}: deceptive Falsified is not writable (prevent profile)", path)),
        Some(o) => Err(format!("{}: unknown fate \"{}\"", path, o)),
        None => Err(format!("{}: fate missing \"k\"", path)),
    }
}
fn dec_bond(path: &str, v: &Json) -> Result<Bond, String> {
    match v.field("k").and_then(|k| k.as_str()) {
        Some("Intact") => Ok(Bond::Intact), Some("Withheld") => Ok(Bond::Withheld), Some("Severed") => Ok(Bond::Severed),
        Some("Misbound") => Err(format!("{}: deceptive Misbound is not writable (prevent profile)", path)),
        Some(o) => Err(format!("{}: unknown bond \"{}\"", path, o)),
        None => Err(format!("{}: bond missing \"k\"", path)),
    }
}
fn dec_merge(path: &str, v: &Json) -> Result<Merge, String> {
    match v.field("k").and_then(|k| k.as_str()) {
        Some("Single") => Ok(Merge::Single),
        Some("Fused") => match v.field("tau").and_then(|t| t.as_str()) {
            Some(t) if !t.is_empty() => Ok(Merge::Fused),
            Some(_) => Err(format!("{}: Fused tag must be non-empty", path)),
            None => Err(format!("{}: Fused requires a provenance tag (untagged merge)", path)),
        },
        Some("Conflated") => Err(format!("{}: deceptive Conflated is not writable (untagged merge)", path)),
        Some(o) => Err(format!("{}: unknown merge \"{}\"", path, o)),
        None => Err(format!("{}: merge missing \"k\"", path)),
    }
}
fn req<'a>(path: &str, k: &str, v: &'a Json) -> Result<&'a Json, String> {
    v.field(k).ok_or_else(|| format!("{}: missing \"{}\"", path, k))
}
fn dec_grade(epath: &str, v: &Json) -> Result<Grade, String> {
    let fa = req(&format!("{}/grade", epath), "fate", v)?;
    let q = dec_fate(&format!("{}/grade/fate/quality", epath), true, req(&format!("{}/grade/fate", epath), "quality", fa)?)?;
    let b = dec_fate(&format!("{}/grade/fate/bearer", epath), false, req(&format!("{}/grade/fate", epath), "bearer", fa)?)?;
    let c = dec_fate(&format!("{}/grade/fate/context", epath), false, req(&format!("{}/grade/fate", epath), "context", fa)?)?;
    let r = dec_fate(&format!("{}/grade/fate/record", epath), false, req(&format!("{}/grade/fate", epath), "record", fa)?)?;
    let bo = dec_bond(&format!("{}/grade/bond", epath), req(&format!("{}/grade", epath), "bond", v)?)?;
    let me = dec_merge(&format!("{}/grade/merge", epath), req(&format!("{}/grade", epath), "merge", v)?)?;
    let bearer_absent = b == Fate::Dropped;
    let coherent = if bearer_absent { bo != Bond::Intact } else { bo == Bond::Intact };
    if !coherent { return Err(format!("{}/grade/bond: incoherent with the bearer's fate (HC-4)", epath)); }
    Ok(Grade { q, b, c, r, bond: bo, merge: me })
}
fn str_list(v: &Json) -> Vec<String> {
    v.as_arr().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default()
}
fn dec_node(v: &Json) -> Result<Node, String> {
    let id = v.field("id").and_then(|x| x.as_str()).ok_or("nodes: missing id")?.to_string();
    let kind = v.field("type").and_then(|x| x.as_str()).ok_or_else(|| format!("nodes/{}: missing type", id))?.to_string();
    let present = v.field("present").map(str_list).unwrap_or_default();
    if kind == "FloatingQuality" && present.iter().any(|p| p == "bearer") {
        return Err(format!("nodes/{}/present: FloatingQuality may not list a bearer", id));
    }
    if !matches!(kind.as_str(), "Trope" | "FloatingQuality" | "Codomain") {
        return Err(format!("nodes/{}: unknown type \"{}\"", id, kind));
    }
    Ok(Node { id, kind, present })
}
fn dec_edge(v: &Json) -> Result<Edge, String> {
    let id = v.field("id").and_then(|x| x.as_str()).ok_or("edges: missing id")?.to_string();
    let inputs = v.field("inputs").map(str_list).unwrap_or_default();
    let output = v.field("output").and_then(|x| x.as_str()).ok_or_else(|| format!("edges/{}: missing output", id))?.to_string();
    let grade = dec_grade(&format!("edges/{}", id), req(&format!("edges/{}", id), "grade", v)?)?;
    Ok(Edge { id, inputs, output, grade })
}
fn dec_floor(v: &Json) -> Result<Floor, String> {
    let ff = |k: &str, is_q: bool| -> Result<Option<Fate>, String> {
        match v.field("fate").and_then(|fa| fa.field(k)) {
            Some(fv) => Ok(Some(dec_fate(&format!("use_model/floor/fate/{}", k), is_q, fv)?)),
            None => Ok(None),
        }
    };
    let bo = match v.field("bond") { Some(bv) => Some(dec_bond("use_model/floor/bond", bv)?), None => None };
    let me = match v.field("merge") { Some(mv) => Some(dec_merge("use_model/floor/merge", mv)?), None => None };
    Ok(Floor { q: ff("quality", true)?, b: ff("bearer", false)?, c: ff("context", false)?, r: ff("record", false)?, bond: bo, merge: me })
}
fn dec_doc(v: &Json) -> Result<Doc, String> {
    let nodes = v.field("nodes").and_then(Json::as_arr).ok_or("missing nodes")?.iter().map(dec_node).collect::<Result<Vec<_>, _>>()?;
    let edges = v.field("edges").and_then(Json::as_arr).ok_or("missing edges")?.iter().map(dec_edge).collect::<Result<Vec<_>, _>>()?;
    let um = v.field("use_model").ok_or("missing use_model")?;
    let out = um.field("output").and_then(|x| x.as_str()).ok_or("use_model: missing output")?.to_string();
    let floor = dec_floor(um.field("floor").ok_or("use_model: missing floor")?)?;
    let _ = &nodes; // nodes are validated at decode; structural coherence already enforced
    Ok(Doc { nodes, edges, out, floor })
}

// ──────────────────────────── checker (DAG accumulate + verdict + witness) ────────
fn acc(edges: &[Edge], node: &str, fuel: usize, memo: &mut BTreeMap<String, Grade>) -> Grade {
    if fuel == 0 { return epsilon(); }
    if let Some(g) = memo.get(node) { return g.clone(); }
    let prod = edges.iter().find(|e| e.output == node);
    let g = match prod {
        None => epsilon(),
        Some(e) => {
            let ins: Vec<Grade> = e.inputs.iter().map(|s| acc(edges, s, fuel - 1, memo)).collect();
            match ins.len() {
                0 => e.grade.clone(),
                1 => grade_compose(&ins[0], &e.grade),
                _ => { let mut m = ins[0].clone(); for x in &ins[1..] { m = grade_meet(&m, x); } grade_compose(&m, &e.grade) }
            }
        }
    };
    memo.insert(node.to_string(), g.clone());
    g
}
fn violations(fl: &Floor, g: &Grade) -> Vec<String> {
    let mut v = Vec::new();
    if let Some(d) = &fl.q { if !fate_le(d, &g.q) { v.push("fate.quality".into()); } }
    if let Some(d) = &fl.b { if !fate_le(d, &g.b) { v.push("fate.bearer".into()); } }
    if let Some(d) = &fl.c { if !fate_le(d, &g.c) { v.push("fate.context".into()); } }
    if let Some(d) = &fl.r { if !fate_le(d, &g.r) { v.push("fate.record".into()); } }
    if let Some(d) = &fl.bond { if !bond_le(d, &g.bond) { v.push("bond".into()); } }
    if let Some(d) = &fl.merge { if !merge_le(d, &g.merge) { v.push("merge".into()); } }
    v
}
fn check(doc: &Doc) -> (String, Option<(String, String)>) {
    let fuel = doc.edges.len() + 1;
    let mut memo = BTreeMap::new();
    let final_g = acc(&doc.edges, &doc.out, fuel, &mut memo);
    let bad = violations(&doc.floor, &final_g);
    if bad.is_empty() { return ("p-sufficient".into(), None); }
    // witness: first edge (document order) whose output grade violates a failing coord
    for e in &doc.edges {
        let mut m2 = BTreeMap::new();
        let g = acc(&doc.edges, &e.output, fuel, &mut m2);
        let hit: Vec<String> = violations(&doc.floor, &g).into_iter().filter(|c| bad.contains(c)).collect();
        if let Some(c) = hit.first() { return ("p-insufficient".into(), Some((e.id.clone(), c.clone()))); }
    }
    ("p-insufficient".into(), None)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 { eprintln!("usage: tropecheck-rs <ir.json>"); exit(64); }
    let src = match std::fs::read_to_string(&args[1]) { Ok(s) => s, Err(e) => { println!("io-error\t{}", e); exit(3); } };
    let j = match parse_json(&src) { Ok(j) => j, Err(e) => { println!("validation-fault\tparse: {}", e); exit(2); } };
    let doc = match dec_doc(&j) { Ok(d) => d, Err(e) => { println!("validation-fault\t{}", e); exit(2); } };
    match check(&doc) {
        (v, None) if v == "p-sufficient" => { println!("p-sufficient"); exit(0); }
        (_, Some((e, c))) => { println!("p-insufficient\twitness={}\tcoord={}", e, c); exit(1); }
        (_, None) => { println!("p-insufficient\t(no witness)"); exit(1); }
    }
}
