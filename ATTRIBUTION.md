# Attribution

Code copied from other repositories into this one, and where it came from. There is one entry per
source: a repository, a folder in one, or a pull request. A whole repository or folder is recorded
at folder level, not file by file. Code that only uses another library, or was written after
reading it, is not listed.

## Format

```markdown
### Short name of the source

- **Source**: <https://github.com/owner/repo>, `path/to/folder/`, commit `abc1234`
- **Licence**: Apache 2.0
- **Original authors**: Jane Doe, John Smith
- **Copied**: `path/to/folder/` to `Coarse/Path/To/Folder/`
- **Changes**: ported to the module system; `Foo.bar` renamed `Foo.baz`
```

## Entries

### GeometricGroupTheoryLean

- **Source**: <https://github.com/koly777/GeometricGroupTheoryLean>, commit `1c61b0a`
- **Licence**: Apache 2.0, as stated in the header of every Lean file (the repository has no
  LICENSE file)
- **Original authors**: Saif Ghobash
- **Copied**: the whole repository's Lean code: `CoarseSpace/` to `Coarse/Topology/CoarseSpace/`,
  `ForMathlib/` to `Coarse/` (with `Data/Rel.lean` at `Basic/Rel.lean`, as in current Mathlib)
- **Changes**: ported from Mathlib `v4.26.0` to the pinned revision and to the module system;
  names moved out of the root namespace (`Coarse` is `IsCoarseMap`, `IsClose` is
  `IsCoarselyClose`, the set predicates are in `CoarseSpace`), API lemmas renamed or made public,
  Mathlib style applied

### mathlib4 #44853

- **Source**: <https://github.com/leanprover-community/mathlib4/pull/44853>, commit `279e410`
- **Licence**: Apache 2.0
- **Original authors**: Hang Lu Su (files), Dmitry Kaysin (PR changes)
- **Copied**: `Mathlib/GroupTheory/Generators.lean`, `Mathlib/Geometry/Group/WordProd.lean` and
  `Mathlib/Geometry/Group/WordMetric.lean` as patched by the PR, to the same paths under `Coarse/`
- **Changes**: imports point to the copies instead of Mathlib

### mathlib4 #44958

- **Source**: <https://github.com/leanprover-community/mathlib4/pull/44958>, commit `885510a`
- **Licence**: Apache 2.0
- **Original authors**: Dmitry Kaysin
- **Copied**: the code the PR adds to `Mathlib/Combinatorics/SimpleGraph/Cayley.lean`, to
  `Coarse/Combinatorics/SimpleGraph/Cayley.lean`
- **Changes**: in a file of its own, with the PR's import changes applied there

### mathlib4 #45132

- **Source**: <https://github.com/leanprover-community/mathlib4/pull/45132>, commit `9812fde`
  (stacked on #44853)
- **Licence**: Apache 2.0
- **Original authors**: Dmitry Kaysin
- **Copied**: `Mathlib/Geometry/Group/CayleySimpleGraph.lean` and
  `Mathlib/Geometry/Group/ReducedWord.lean` to the same paths under `Coarse/`; the section
  "Non-backtracking walks" of `Mathlib/Combinatorics/SimpleGraph/Paths.lean` to
  `Coarse/Combinatorics/SimpleGraph/Paths.lean`; `List.IsChain.imp_of_isChain` to
  `Coarse/Data/List/Chain.lean`
- **Changes**: imports point to the copies; the two extracts are in files of their own

### mathlib4 #43723

- **Source**: <https://github.com/leanprover-community/mathlib4/pull/43723>, commit `e0bdbe1`
- **Licence**: Apache 2.0
- **Original authors**: Hang Lu Su, Katerina Hristova
- **Copied**: `Mathlib/Topology/MetricSpace/Hyperbolic.lean`, to the same path under `Coarse/`
- **Changes**: a local `attribute [grind =] Bornology.isBounded_univ` replaces the PR's edit to
  `Mathlib/Topology/Bornology/Basic.lean`

### mathlib4 #44339

- **Source**: <https://github.com/leanprover-community/mathlib4/pull/44339>, commit `1ef250d`
  (stacked on #43723)
- **Licence**: Apache 2.0
- **Original authors**: Hang Lu Su, Katerina Hristova
- **Copied**: `Mathlib/Geometry/Group/Hyperbolic.lean`, to the same path under `Coarse/`
- **Changes**: imports point to the copies; the PR's other edits to Mathlib files are not copied

### Mathlib `Presentation`

- **Source**: <https://github.com/leanprover-community/mathlib4>,
  `Mathlib/GroupTheory/Presentation.lean`, commit `10dc788`
- **Licence**: Apache 2.0
- **Original authors**: Hang Lu Su, Valerio Proietti
- **Copied**: the file, to `Coarse/GroupTheory/Presentation.lean`
- **Changes**: imports the copy of `Generators`, so that it builds alongside the #44853 copies

### mathlib4 #42005

- **Source**: <https://github.com/leanprover-community/mathlib4/pull/42005>, commit `f11990d`
- **Licence**: Apache 2.0
- **Original authors**: Hang Lu Su, Justus Springer
- **Copied**: `Mathlib/Geometry/Group/DehnFunction.lean`, to the same path under `Coarse/`
- **Changes**: imports the copy of `Presentation` instead of Mathlib's
