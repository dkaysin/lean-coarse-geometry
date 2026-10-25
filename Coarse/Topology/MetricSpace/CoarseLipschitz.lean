/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Coarse Lipschitz maps

A map `f` between pseudometric spaces is *coarse Lipschitz* with constants `L` and `C` if
`dist (f x) (f y) ≤ L * dist x y + C` for all `x` and `y`.
Coarse Lipschitz maps need not be continuous.

## Main definitions

* `Metric.CoarseLipschitzWith L C f`: `dist (f x) (f y) ≤ L * dist x y + C` for all `x`, `y`.

## Main statements

* `Metric.CoarseLipschitzWith.comp`: coarse Lipschitz maps are closed under composition, with
  explicit constants.

## Implementation notes

The constants `L` and `C` have type `ℝ≥0`, as the constant of `LipschitzWith`. Unlike
`LipschitzWith`, the definition is stated with `dist` on pseudometric spaces, not with `edist`.

## References

* C. Druțu, M. Kapovich, *Geometric group theory*, AMS Colloquium Publications 63, 2018,
  Definition 8.5

## Tags

coarse Lipschitz, coarse geometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

namespace Metric

variable {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
  {L C L' C' L₁ C₁ L₂ C₂ : ℝ≥0} {f : α → β} {g : β → γ}

/-- A map `f` between pseudometric spaces is **coarse Lipschitz** with constants `L` and `C` if
`dist (f x) (f y) ≤ L * dist x y + C` for all `x` and `y`. -/
def CoarseLipschitzWith (L C : ℝ≥0) (f : α → β) : Prop :=
  ∀ x y, dist (f x) (f y) ≤ L * dist x y + C

/-- A Lipschitz map is coarse Lipschitz with additive constant `0`. -/
theorem _root_.LipschitzWith.coarseLipschitzWith (hf : LipschitzWith L f) :
    CoarseLipschitzWith L 0 f := fun x y ↦ by
  simpa using hf.dist_le_mul x y

namespace CoarseLipschitzWith

/-- (L, C)-coarse Lipschitz map is also (L', C')-coarse Lipschitz
for L ≤ L' and C ≤ C'. -/
theorem mono (hf : CoarseLipschitzWith L C f) (hL : L ≤ L') (hC : C ≤ C') :
    CoarseLipschitzWith L' C' f := fun x y ↦ by
  grw [hf x y, hL, hC]

/-- The composition of two coarse Lipschitz maps is coarse Lipschitz. -/
protected theorem comp (hg : CoarseLipschitzWith L₂ C₂ g) (hf : CoarseLipschitzWith L₁ C₁ f) :
    CoarseLipschitzWith (L₂ * L₁) (L₂ * C₁ + C₂) (g ∘ f) := fun x y ↦ by
  grw [Function.comp_apply, Function.comp_apply, hg (f x) (f y), hf x y]
  push_cast
  linarith

end CoarseLipschitzWith

end Metric
