/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Topology.MetricSpace.QuasiIsometry
public import Mathlib.Topology.Instances.Int

/-!
# Quasi-isometric embeddings of common spaces

This file collects quasi-isometric embeddings between common spaces, with explicit constants.

## Main statements

* `Metric.isQuasiIsometricEmbeddingWith_intFloor`: the floor `ℝ → ℤ` is a
  `(1, 1)`-quasi-isometric embedding.

## Tags

quasi-isometric embedding, floor, integers, real numbers
-/

@[expose] public section

open scoped NNReal

namespace Metric

/-- The floor `ℝ → ℤ` is a `(1, 1)`-quasi-isometric embedding. -/
theorem isQuasiIsometricEmbeddingWith_intFloor :
    IsQuasiIsometricEmbeddingWith 1 1 (Int.floor : ℝ → ℤ) := by
  -- `⌊s⌋ - ⌊s'⌋` and `s - s'` differ by less than `1`.
  refine ⟨fun s s' ↦ ?_, fun s s' ↦ ?_⟩ <;>
  · simp only [Int.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, mul_one]
    have := Int.floor_le s
    have := Int.floor_le s'
    have := Int.lt_floor_add_one s
    have := Int.lt_floor_add_one s'
    rw [abs_le]
    constructor <;> linarith [le_abs_self (s - s'), neg_abs_le (s - s'),
      le_abs_self ((⌊s⌋ : ℝ) - ⌊s'⌋), neg_abs_le ((⌊s⌋ : ℝ) - ⌊s'⌋)]

end Metric
