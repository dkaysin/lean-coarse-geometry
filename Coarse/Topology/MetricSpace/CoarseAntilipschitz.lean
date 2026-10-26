/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Coarse antilipschitz maps

A map `f` between pseudometric spaces is *coarse antilipschitz* with constants `L` and `C`
if `dist x y ≤ L * dist (f x) (f y) + C` for all `x` and `y`.
Coarse antilipschitz maps need not be injective.

## Main definitions

* `Metric.CoarseAntilipschitzWith L C f`: `dist x y ≤ L * dist (f x) (f y) + C` for all `x`, `y`.

## Main statements

* `Metric.CoarseAntilipschitzWith.comp`: coarse antilipschitz maps are closed under composition,
  with explicit constants.
* `Metric.coarseAntilipschitzWith_iff_inv_mul_sub_le`: the lower bound in the form
  `L⁻¹ * dist x y - C ≤ dist (f x) (f y)` used in the literature.

## Implementation notes

As for `AntilipschitzWith`, the constant `L` multiplies the distance in the codomain and is not
required to be positive, and the constants have type `ℝ≥0`. Unlike `AntilipschitzWith`, the
definition is stated with `dist` on pseudometric spaces, not with `edist`.

The name is formed after `AntilipschitzWith`; it is not standard in the literature.

## References

* [C. Druțu, M. Kapovich, *Geometric Group Theory*][drutu2018], Definition 8.5

## Tags

coarse antilipschitz, coarse geometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

namespace Metric

variable {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
  {L C L' C' L₁ C₁ L₂ C₂ : ℝ≥0} {f : α → β} {g : β → γ}

/-- A map `f` between pseudometric spaces is **coarse antilipschitz** with constants `L` and `C`
if `dist x y ≤ L * dist (f x) (f y) + C` for all `x` and `y`. -/
def CoarseAntilipschitzWith (L C : ℝ≥0) (f : α → β) : Prop :=
  ∀ x y, dist x y ≤ L * dist (f x) (f y) + C

/-- An antilipschitz map is coarse antilipschitz with additive constant `0`. -/
theorem _root_.AntilipschitzWith.coarseAntilipschitzWith (hf : AntilipschitzWith L f) :
    CoarseAntilipschitzWith L 0 f := fun x y ↦ by
  simpa using hf.le_mul_dist x y

/-- A lower bound of the form `L⁻¹ * dist x y - C ≤ dist (f x) (f y)`, with a division and a
subtraction, says that the map is coarse antilipschitz with constants `L` and `L * C`. -/
theorem coarseAntilipschitzWith_iff_inv_mul_sub_le (hL : L ≠ 0) :
    CoarseAntilipschitzWith L (L * C) f ↔
      ∀ x y, (L : ℝ)⁻¹ * dist x y - C ≤ dist (f x) (f y) := by
  have hL' : (0 : ℝ) < L := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hL)
  simp only [CoarseAntilipschitzWith, NNReal.coe_mul, sub_le_iff_le_add, inv_mul_le_iff₀ hL',
    mul_add]

namespace CoarseAntilipschitzWith

theorem mono (hf : CoarseAntilipschitzWith L C f) (hL : L ≤ L') (hC : C ≤ C') :
    CoarseAntilipschitzWith L' C' f := fun x y ↦ by
  grw [hf x y, hL, hC]

/-- The composition of two coarse antilipschitz maps is coarse antilipschitz. -/
protected theorem comp (hg : CoarseAntilipschitzWith L₂ C₂ g)
    (hf : CoarseAntilipschitzWith L₁ C₁ f) :
    CoarseAntilipschitzWith (L₁ * L₂) (L₁ * C₂ + C₁) (g ∘ f) := fun x y ↦ by
  grw [hf x y, hg (f x) (f y)]
  push_cast
  simp only [Function.comp_apply]
  linarith

end CoarseAntilipschitzWith

end Metric
