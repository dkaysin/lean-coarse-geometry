/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Combinatorics.SimpleGraph.Metric
public import Coarse.Topology.MetricSpace.CoarselyGeodesic
public import Coarse.Topology.MetricSpace.Geodesic
public import Coarse.Topology.MetricSpace.QuasiIsometry
public import Coarse.Topology.MetricSpace.QuasiIsometry.Examples

/-!
# Quasi-geodesics

A *`(c, b)`-quasi-geodesic* from `x` to `x'` in a pseudometric space is a map `γ : [t, t'] → X`
satisfying the bounds of a `(c, b)`-quasi-isometric embedding, with `γ t = x` and `γ t' = x'`; it
need not be continuous. A *`(c, b)`-quasi-geodesic space* is a space in which any two points are
joined by a `(c, b)`-quasi-geodesic; up to the constants, these are the coarsely geodesic spaces.

## Main definitions

* `Metric.IsQuasiGeodesicWith c b γ t t' x x'`: the map `γ : ℝ → X` is a `(c, b)`-quasi-geodesic on
  `[t, t']` from `x` to `x'`.
* `Metric.IsQuasiGeodesicSpaceWith X c b`: any two points of `X` are joined by a
  `(c, b)`-quasi-geodesic.
* `Metric.IsQuasiGeodesicSpace X`: `X` is a `(c, b)`-quasi-geodesic space for some `c` and `b`.

## Main statements

* `Metric.IsGeodesic.isQuasiGeodesicWith`: a geodesic is a `(1, 0)`-quasi-geodesic.
* `Metric.IsQuasiGeodesicWith.exists_isCoarseGeodesicWith`: a `(c, b)`-quasi-geodesic from `x` to
  `x'` gives an `r`-chain from `x` to `x'` that is a `(c / δ, c * b / δ + 1)`-coarse geodesic if
  `c * δ + b ≤ r`.
* `Metric.IsGeodesicSpace.isCoarselyGeodesicSpaceWith`: a geodesic space is `(r, r⁻¹, 1)`-coarsely
  geodesic for every `r > 0`.
* `Metric.IsQuasiGeodesicSpaceWith.isCoarselyGeodesicSpaceWith`: a `(c, b)`-quasi-geodesic space is
  `(c + b, c, c * b + 1)`-coarsely geodesic.
* `Metric.IsCoarselyGeodesicSpaceWith.isQuasiGeodesicSpaceWith`: an `(r, L, C)`-coarsely geodesic
  space is a `(max (max r L) 1, max r (C + 1))`-quasi-geodesic space.
* `Metric.isCoarselyGeodesicSpace_iff_isQuasiGeodesicSpace`: the coarsely geodesic spaces are the
  quasi-geodesic spaces.

## Implementation notes

A quasi-geodesic is a map `γ : ℝ → X` of which only the values on `[t, t']` matter, as for
`Metric.IsGeodesic`; its two bounds are stated for parameters in `[t, t']` rather than through
`Metric.IsQuasiIsometricEmbeddingWith`, which would need the subtype `[t, t']`. The constants may be
`0`. The quasi-geodesics built from
chains are step functions on `[0, n]`.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Definition 5.3.4
* [M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
  Definition I.8.22

## Tags

quasi-geodesic, quasi-geodesic space, coarsely geodesic, chain, coarse geometry
-/

@[expose] public section

open scoped NNReal

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A map `γ : ℝ → X` is a **`(c, b)`-quasi-geodesic** on `[t, t']` from `x` to `x'` if `γ t = x`,
`γ t' = x'` and, for parameters in `[t, t']`, `γ` satisfies the bounds of a `(c, b)`-quasi-isometric
embedding (`Metric.IsQuasiIsometricEmbeddingWith`). It need not be continuous.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
structure IsQuasiGeodesicWith (c b : ℝ≥0) (γ : ℝ → X) (t t' : ℝ) (x x' : X) : Prop where
  le : t ≤ t'
  apply_left : γ t = x
  apply_right : γ t' = x'
  dist_le : ∀ s ∈ Set.Icc t t', ∀ s' ∈ Set.Icc t t', dist (γ s) (γ s') ≤ c * |s - s'| + b
  le_dist : ∀ s ∈ Set.Icc t t', ∀ s' ∈ Set.Icc t t', |s - s'| ≤ c * dist (γ s) (γ s') + c * b

/-- A pseudometric space is a **`(c, b)`-quasi-geodesic space** if any two points are joined by a
`(c, b)`-quasi-geodesic.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
def IsQuasiGeodesicSpaceWith (X : Type*) [PseudoMetricSpace X] (c b : ℝ≥0) : Prop :=
  ∀ x x' : X, ∃ (γ : ℝ → X) (t t' : ℝ), IsQuasiGeodesicWith c b γ t t' x x'

/-- A pseudometric space is a **quasi-geodesic space** if it is a `(c, b)`-quasi-geodesic space
for some constants `c` and `b`.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
def IsQuasiGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ c b, IsQuasiGeodesicSpaceWith X c b

/-- A geodesic is a `(1, 0)`-quasi-geodesic. -/
theorem IsGeodesic.isQuasiGeodesicWith {γ : ℝ → X} {t t' : ℝ} {x x' : X}
    (hγ : IsGeodesic γ t t' x x') : IsQuasiGeodesicWith 1 0 γ t t' x x' where
  le := hγ.le
  apply_left := hγ.apply_left
  apply_right := hγ.apply_right
  dist_le s hs s' hs' := by simp [hγ.dist_eq s hs s' hs']
  le_dist s hs s' hs' := by simp [hγ.dist_eq s hs s' hs']

/-- A `(c, b)`-quasi-geodesic from `x` to `x'`, sampled at parameters at most `δ` apart, gives an
`r`-chain from `x` to `x'` that is a `(c / δ, c * b / δ + 1)`-coarse geodesic, if
`c * δ + b ≤ r`. -/
theorem IsQuasiGeodesicWith.exists_isCoarseGeodesicWith {c b r δ : ℝ≥0} {γ : ℝ → X} {t t' : ℝ}
    {x x' : X} (hγ : IsQuasiGeodesicWith c b γ t t' x x') (hδ : 0 < δ) (hr : c * δ + b ≤ r) :
    ∃ p : (ripsGraph X r).Walk x x', IsCoarseGeodesicWith (c / δ) (c * b / δ + 1) p := by
  have hδ' : (0 : ℝ) < δ := NNReal.coe_pos.2 hδ
  -- The lower bound of `γ` at the endpoints gives `t' - t ≤ c * dist x x' + c * b`.
  have hlower := hγ.le_dist t (Set.left_mem_Icc.2 hγ.le) t' (Set.right_mem_Icc.2 hγ.le)
  rw [hγ.apply_left, hγ.apply_right, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hγ.le)] at hlower
  -- Sample `γ` at `t, t + δ, t + 2 * δ, …`, capped at `t'`: `n = ⌈(t' - t) / δ⌉₊` steps.
  set n := ⌈(t' - t) / δ⌉₊
  have hmem (k : ℕ) : min (t + k * δ) t' ∈ Set.Icc t t' :=
    ⟨le_min (le_add_of_nonneg_right (by positivity)) hγ.le, min_le_right _ _⟩
  have hstep (k : ℕ) (_ : k < n) :
      dist (γ (min (t + k * δ) t')) (γ (min (t + ((k + 1 : ℕ) : ℝ) * δ) t')) ≤ r := by
    -- Consecutive parameters are at most `δ` apart.
    have h := abs_min_sub_min_le_max (t + k * δ) t' (t + ((k + 1 : ℕ) : ℝ) * δ) t'
    rw [sub_self, abs_zero, add_sub_add_left_eq_sub, ← sub_mul, Nat.cast_succ, sub_add_cancel_left,
      neg_one_mul, abs_neg, abs_of_pos hδ', max_eq_left hδ'.le] at h
    calc dist _ _ ≤ c * |min (t + k * δ) t' - min (t + ((k + 1 : ℕ) : ℝ) * δ) t'| + b :=
          hγ.dist_le _ (hmem k) _ (hmem (k + 1))
      _ ≤ c * δ + b := by gcongr; exact_mod_cast h
      _ ≤ r := by exact_mod_cast hr
  obtain ⟨p, hp⟩ := exists_ripsGraph_walk_length_le _ n hstep
  have hn : t' ≤ t + n * δ := by
    have := Nat.le_ceil ((t' - t) / δ)
    rw [div_le_iff₀ hδ'] at this
    linarith
  refine ⟨p.copy (by simpa [min_eq_left hγ.le] using hγ.apply_left)
    (by simpa [min_eq_right hn] using hγ.apply_right), ⟨?_⟩⟩
  -- The number of steps is `n < (t' - t) / δ + 1 ≤ (c * dist x x' + c * b) / δ + 1`.
  rw [SimpleGraph.Walk.length_copy]
  calc (p.length : ℝ) ≤ n := Nat.cast_le.2 hp
    _ ≤ (t' - t) / δ + 1 := (Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.2 hγ.le) hδ'.le)).le
    _ ≤ (c * dist x x' + c * b) / δ + 1 := by gcongr
    _ = ↑(c / δ) * dist x x' + ↑(c * b / δ + 1) := by push_cast; ring

/-- A `(c, b)`-quasi-geodesic space is `(c + b, c, c * b + 1)`-coarsely geodesic. -/
theorem IsQuasiGeodesicSpaceWith.isCoarselyGeodesicSpaceWith {c b : ℝ≥0}
    (h : IsQuasiGeodesicSpaceWith X c b) : IsCoarselyGeodesicSpaceWith X (c + b) c (c * b + 1) :=
  fun x x' ↦ by
    -- Sample a quasi-geodesic at parameters at most `1` apart.
    obtain ⟨γ, t, t', hγ⟩ := h x x'
    simpa using hγ.exists_isCoarseGeodesicWith (r := c + b) one_pos (by simp)

/-- A geodesic space is `(r, r⁻¹, 1)`-coarsely geodesic for every `r > 0`. -/
theorem IsGeodesicSpace.isCoarselyGeodesicSpaceWith (hX : IsGeodesicSpace X) {r : ℝ≥0}
    (hr : 0 < r) : IsCoarselyGeodesicSpaceWith X r r⁻¹ 1 :=
  fun x x' ↦ by
    -- Sample a geodesic at parameters at most `r` apart.
    obtain ⟨γ, t, t', hγ⟩ := hX x x'
    simpa using hγ.isQuasiGeodesicWith.exists_isCoarseGeodesicWith (r := r) hr (by simp)

/-- An `(r, L, C)`-coarsely geodesic space is a `(max (max r L) 1, max r (C + 1))`-quasi-geodesic
space. -/
theorem IsCoarselyGeodesicSpaceWith.isQuasiGeodesicSpaceWith {r L C : ℝ≥0}
    (h : IsCoarselyGeodesicSpaceWith X r L C) :
    IsQuasiGeodesicSpaceWith X (max (max r L) 1) (max r (C + 1)) := by
  intro x x'
  -- Take a shortest chain `x = x₀, …, xₙ = x'` and the step function `s ↦ x_⌊s⌋₊` on `[0, n]`.
  obtain ⟨q, -⟩ := h x x'
  obtain ⟨p, hp⟩ := q.reachable.exists_walk_length_eq_dist
  -- On indices, `dist xᵢ xⱼ ≤ r * |i - j|`, and `|i - j|`, the Rips-graph distance between `xᵢ`
  -- and `xⱼ` since the chain is shortest, is at most `L * dist xᵢ xⱼ + C`.
  have hidx (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) :
      dist (p.getVert i) (p.getVert j) ≤ r * |(i : ℝ) - j| ∧
        |(i : ℝ) - j| ≤ L * dist (p.getVert i) (p.getVert j) + C := by
    wlog hij : i ≤ j generalizing i j
    · obtain ⟨h₁, h₂⟩ := this j i hj hi (by omega)
      rw [dist_comm, abs_sub_comm]
      exact ⟨h₁, h₂⟩
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 hij)), ← Nat.cast_sub hij]
    refine ⟨p.dist_getVert_le_mul (φ := id)
      (fun _ _ (hadj : (ripsGraph X r).Adj _ _) ↦ hadj.2) hij hj, ?_⟩
    obtain ⟨q, ⟨hq⟩⟩ := h (p.getVert i) (p.getVert j)
    rw [← p.dist_getVert_of_length_eq_dist hp hij hj]
    exact (Nat.cast_le.2 (SimpleGraph.dist_le q)).trans hq
  -- On parameters `s, s' ≥ 0`, `|⌊s⌋₊ - ⌊s'⌋₊|` and `|s - s'|` differ by at most `1`.
  have hfl {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') :
      |(⌊s⌋₊ : ℝ) - ⌊s'⌋₊| ≤ |s - s'| + 1 ∧ |s - s'| ≤ |(⌊s⌋₊ : ℝ) - ⌊s'⌋₊| + 1 := by
    have h₁ := isQuasiIsometricEmbeddingWith_intFloor.coarseLipschitzWith s s'
    have h₂ := isQuasiIsometricEmbeddingWith_intFloor.coarseAntilipschitzWith s s'
    simp only [Int.dist_eq, Real.dist_eq, ← natCast_floor_eq_intCast_floor hs,
      ← natCast_floor_eq_intCast_floor hs', NNReal.coe_one, one_mul, mul_one] at h₁ h₂
    exact ⟨h₁, h₂⟩
  have hγ {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) p.length) : ⌊s⌋₊ ≤ p.length := Nat.floor_le_of_le hs.2
  -- The step function is `(r, r)`-coarse Lipschitz and `(L, C + 1)`-coarse antilipschitz.
  have hc : (1 : ℝ) ≤ max (max r L) 1 := by exact_mod_cast le_max_right _ _
  have hrc : (r : ℝ) ≤ max (max r L) 1 := by
    exact_mod_cast (le_max_left _ _).trans (le_max_left _ _)
  have hLc : (L : ℝ) ≤ max (max r L) 1 := by
    exact_mod_cast (le_max_right _ _).trans (le_max_left _ _)
  have hrb : (r : ℝ) ≤ max r (C + 1) := by exact_mod_cast le_max_left _ _
  have hCb : (C : ℝ) + 1 ≤ max r (C + 1) := by exact_mod_cast le_max_right _ _
  refine ⟨fun s ↦ p.getVert ⌊s⌋₊, 0, p.length, ⟨Nat.cast_nonneg _, by simp, by simp,
    fun s hs s' hs' ↦ ?_, fun s hs s' hs' ↦ ?_⟩⟩
  · calc dist (p.getVert ⌊s⌋₊) (p.getVert ⌊s'⌋₊) ≤ r * |(⌊s⌋₊ : ℝ) - ⌊s'⌋₊| :=
          (hidx _ _ (hγ hs) (hγ hs')).1
      _ ≤ r * (|s - s'| + 1) := by gcongr; exact (hfl hs.1 hs'.1).1
      _ ≤ ↑(max (max r L) 1) * |s - s'| + ↑(max r (C + 1)) := by
          rw [mul_add, mul_one]; gcongr
  · have hd := (hidx _ _ (hγ hs) (hγ hs')).2
    calc |s - s'| ≤ |(⌊s⌋₊ : ℝ) - ⌊s'⌋₊| + 1 := (hfl hs.1 hs'.1).2
      _ ≤ L * dist (p.getVert ⌊s⌋₊) (p.getVert ⌊s'⌋₊) + (C + 1) := by linarith
      _ ≤ ↑(max (max r L) 1) * dist (p.getVert ⌊s⌋₊) (p.getVert ⌊s'⌋₊) +
          ↑(max (max r L) 1) * ↑(max r (C + 1)) := by
          gcongr
          calc (C : ℝ) + 1 ≤ max r (C + 1) := hCb
            _ = 1 * max r (C + 1) := (one_mul _).symm
            _ ≤ _ := by gcongr

/-- A pseudometric space is coarsely geodesic if and only if it is a quasi-geodesic space.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
theorem isCoarselyGeodesicSpace_iff_isQuasiGeodesicSpace :
    IsCoarselyGeodesicSpace X ↔ IsQuasiGeodesicSpace X :=
  ⟨fun ⟨_, _, _, h⟩ ↦ ⟨_, _, h.isQuasiGeodesicSpaceWith⟩,
   fun ⟨_, _, h⟩ ↦ ⟨_, _, _, h.isCoarselyGeodesicSpaceWith⟩⟩

end Metric
