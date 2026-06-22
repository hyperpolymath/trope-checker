-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
-- SPDX-License-Identifier: MPL-2.0
||| The portable tropechecker executable: `tropecheck <ir.json>`.
||| Reads a Trope IR JSON document, validates + decodes it (the validation
||| boundary, HC-3/HC-4), composes grades over the DAG, and prints the verdict.
||| Exit codes: 0 p-sufficient · 1 p-insufficient · 2 validation-fault · 3 io.
module Main

import System
import System.File
import Checker.Ir
import Checker.Json
import Checker.Decode
import Checker.Check

%default covering

run : String -> IO ()
run path = do
  Right src <- readFile path
    | Left err => do putStrLn ("io-error\t" ++ show err); exitWith (ExitFailure 3)
  case parseJSON src of
    Left e => do putStrLn ("validation-fault\tparse: " ++ e); exitWith (ExitFailure 2)
    Right jv => case decodeDoc jv of
      Left e => do putStrLn ("validation-fault\t" ++ e); exitWith (ExitFailure 2)
      Right doc => case check doc of
        Sufficient => do putStrLn "p-sufficient"; exitSuccess
        Insufficient _ w => do
          let wtxt = case w of
                       Just (ed, co) => "\twitness=" ++ ed ++ "\tcoord=" ++ co
                       Nothing       => "\t(no witness)"
          putStrLn ("p-insufficient" ++ wtxt)
          exitWith (ExitFailure 1)

main : IO ()
main = do
  args <- getArgs
  case args of
    (_ :: path :: _) => run path
    _ => do putStrLn "usage: tropecheck <ir.json>"; exitWith (ExitFailure 64)
