# coarse

A Lean 4 playground for coarse geometry and geometric group theory, built on Mathlib and
written so that its material can move into Mathlib.

The project grows by milestones, groups of definitions and theorems chosen one at a time, one
blueprint chapter each: so far the Švarc–Milnor lemma with its corollaries, the definitions of
hyperbolic spaces and groups and the equivalences between them, and uniformly discrete spaces and
bounded geometry for metric and coarse spaces; next, the Gromov boundary. For each milestone it
adds the definitions that Mathlib lacks, states the results in Lean first and proves them
afterwards.

- `Coarse/`: the library.
- `blueprint/`: the blueprint, listing every definition and theorem with its statement, proof
  sketch, dependencies and status, with the Lean tags of the formalized ones in
  `blueprint/CoarseBlueprint.lean`. `make serve` renders it.
- `docbuild/`: builds the API documentation with doc-gen4 (`make docs`). CI publishes it at `/docs`
  of the GitHub Pages site, next to the blueprint at the root.
- `ATTRIBUTION.md`: code copied from open Mathlib pull requests and other projects.

`make` lists the build targets; `make build` builds the library.
