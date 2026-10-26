# coarse

A Lean 4 playground for coarse geometry and geometric group theory, built on Mathlib and
written so that its material can move into Mathlib.

The project grows by targets, definitions and theorems chosen one at a time: so far the
Švarc–Milnor lemma with its corollaries, and the comparison of the slim-triangle and four-point
definitions of hyperbolic spaces, and uniformly discrete spaces and bounded geometry for metric
and coarse spaces; next, the Gromov boundary. For each target it adds the
definitions that Mathlib lacks, states the results in Lean first and proves them afterwards.

- `Coarse/`: the library.
- `blueprint/` and `CoarseBlueprint/`: the blueprint, listing every definition and theorem with
  its statement, proof sketch, dependencies and status. `make serve` renders it.
- `docbuild/`: builds the API documentation with doc-gen4 (`make docs`). CI publishes it at `/docs`
  of the GitHub Pages site, next to the blueprint at the root.
- `ATTRIBUTION.md`: code copied from open Mathlib pull requests and other projects.

`make` lists the build targets; `make build` builds the library.
