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
  `ForMathlib/` to `Coarse/`
- **Changes**: ported from Mathlib `v4.26.0` to the pinned revision and to the module system;
  `SetRel.ball` and its lemmas dropped (now in Mathlib) and `SetRel.mem_comp_comp` renamed
  `SetRel.mem_comp_comp_of_mem` (Mathlib has a different lemma of that name)
