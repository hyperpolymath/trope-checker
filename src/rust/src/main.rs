// SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0
//
// The `tropecheck-rs` binary: a thin CLI over the library in lib.rs.
//
// All logic — the grade algebra, the decoder, the verdict procedure — now lives
// in the library so that other crates can depend on it directly instead of
// shelling out to this binary or, far worse, reimplementing the algebra and
// forking semantics that are proved in Idris2.
//
// This file deliberately contains NO logic. Same stdout strings and same exit
// codes as before the library was extracted: 0 sufficient, 1 insufficient,
// 2 validation-fault, 3 io, 64 usage.

use std::process::exit;
use tropecheck_rs::{check, dec_doc, parse_json};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: tropecheck-rs <ir.json>");
        exit(64);
    }
    let src = match std::fs::read_to_string(&args[1]) {
        Ok(s) => s,
        Err(e) => {
            println!("io-error\t{}", e);
            exit(3);
        }
    };
    let j = match parse_json(&src) {
        Ok(j) => j,
        Err(e) => {
            println!("validation-fault\tparse: {}", e);
            exit(2);
        }
    };
    let doc = match dec_doc(&j) {
        Ok(d) => d,
        Err(e) => {
            println!("validation-fault\t{}", e);
            exit(2);
        }
    };
    match check(&doc) {
        (v, None) if v == "p-sufficient" => {
            println!("p-sufficient");
            exit(0);
        }
        (_, Some((e, c))) => {
            println!("p-insufficient\twitness={}\tcoord={}", e, c);
            exit(1);
        }
        (_, None) => {
            println!("p-insufficient\t(no witness)");
            exit(1);
        }
    }
}
