/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Geometry.Group.Hyperbolic

/-!
# Hyperbolicity does not depend on the generating family

A group is hyperbolic (`Group.IsHyperbolic`) if its word metric for some finite generating family
satisfies the four-point condition. This file states that then the word metric of every finite
generating family does.

## Main statements

* `Group.Generators.isHyperbolic_iff`: for a finite generating family `P`, the group is hyperbolic
  if and only if it is `δ`-hyperbolic with respect to `P` for some `δ`.

## Tags

hyperbolic group, word metric, generating family, quasi-isometry invariance
-/

@[expose] public section

namespace Group.Generators

variable {G ι : Type*} [Group G]

/-- A group is hyperbolic if and only if its word metric for a given finite generating family
`P` is `δ`-hyperbolic for some `δ`. -/
theorem isHyperbolic_iff [Finite ι] (P : Generators G ι) :
    Group.IsHyperbolic G ↔ ∃ δ, P.IsHyperbolicWith δ := by
  sorry

end Group.Generators
