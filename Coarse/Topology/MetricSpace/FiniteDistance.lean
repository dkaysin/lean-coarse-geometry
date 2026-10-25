/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Maps at finite distance from each other

Two maps `f g : α → β` into a pseudometric space have *finite distance* from each other if the
distance between `f x` and `g x` is bounded independently of `x`. In large scale geometry such
maps are regarded as the same: a quasi-isometry is a quasi-isometric embedding that is invertible
up to finite distance.

## Main definitions

* `Metric.HasFiniteDist f g`: there is a constant `C` with `dist (f x) (g x) ≤ c` for all `x`.

## Main statements

* `Metric.HasFiniteDist.refl`, `Metric.HasFiniteDist.symm`, `Metric.HasFiniteDist.trans`:
  having finite distance is an equivalence relation on maps.

## Implementation notes

The domain of the maps is an arbitrary type, since only the distance of the codomain is used.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Definition 5.1.6

## Tags

finite distance, bounded distance, quasi-isometry, coarse geometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

namespace Metric

variable {α β : Type*} [PseudoMetricSpace β] {f g k : α → β}

/-- Two maps `f` and `g` into a pseudometric space have **finite distance** from each other if
there is a constant `c` such that `dist (f x) (g x) ≤ c` for all `x`.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.1.6. -/
def HasFiniteDist (f g : α → β) : Prop :=
  ∃ c : ℝ≥0, ∀ x, dist (f x) (g x) ≤ c

namespace HasFiniteDist

@[refl]
protected theorem refl (f : α → β) : HasFiniteDist f f :=
  ⟨0, fun x ↦ (dist_self (f x)).le⟩

protected theorem rfl : HasFiniteDist f f :=
  .refl f

@[symm]
protected theorem symm (h : HasFiniteDist f g) : HasFiniteDist g f :=
  let ⟨C, hC⟩ := h
  ⟨C, fun x ↦ (dist_comm (g x) (f x)).trans_le (hC x)⟩

@[trans]
protected theorem trans (hfg : HasFiniteDist f g) (hgk : HasFiniteDist g k) :
    HasFiniteDist f k :=
  let ⟨C₁, h₁⟩ := hfg
  let ⟨C₂, h₂⟩ := hgk
  ⟨C₁ + C₂, fun x ↦ (dist_triangle (f x) (g x) (k x)).trans (add_le_add (h₁ x) (h₂ x))⟩

/-- Precomposition with any map preserves finite distance, with the same constant. -/
theorem comp_right {γ : Type*} (h : HasFiniteDist f g) (k : γ → α) :
    HasFiniteDist (f ∘ k) (g ∘ k) :=
  let ⟨C, hC⟩ := h
  ⟨C, fun x ↦ hC (k x)⟩

end HasFiniteDist

end Metric
