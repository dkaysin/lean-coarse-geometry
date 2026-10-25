/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Lean

/-!
# Declaration locations

Reads declaration names from stdin, one per line, and prints `name`, module and line of each,
separated by tabs. Names not in the environment are skipped. Used by `blueprint_links.py`;
run with `lake env lean --run scripts/DeclLocations.lean`.
-/

open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Coarse }] {}
  let names := (← (← IO.getStdin).readToEnd).splitOn "\n" |>.filter (· ≠ "")
  for s in names do
    let n := s.toName
    let some idx := env.getModuleIdxFor? n | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    let ctx : Core.Context := { fileName := "", fileMap := default }
    let (ranges, _) ← (findDeclarationRanges? n : CoreM _).toIO ctx { env }
    let line := ranges.map (·.range.pos.line) |>.getD 1
    IO.println s!"{s}\t{mod}\t{line}"
