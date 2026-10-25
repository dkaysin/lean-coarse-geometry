# coarse

A Lean 4 playground for coarse geometry and geometric group theory, built on Mathlib and
written so that its material can move into Mathlib.

The project grows by targets, definitions and theorems chosen one at a time: so far the
Švarc–Milnor lemma with its corollaries, and the comparison of the slim-triangle and four-point
definitions of hyperbolic spaces; next, the Gromov boundary. For each target it adds the
definitions that Mathlib lacks, states the results in Lean first and proves them afterwards.

- `Coarse/`: the library.
- `blueprint/` and `CoarseBlueprint/`: the blueprint, listing every definition and theorem with
  its statement, proof sketch, dependencies and status. `make serve` renders it.
- `ATTRIBUTION.md`: code copied from open Mathlib pull requests and other projects.

`make` lists the build targets; `make build` builds the library.
