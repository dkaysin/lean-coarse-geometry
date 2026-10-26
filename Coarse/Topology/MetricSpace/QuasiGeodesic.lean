/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Combinatorics.SimpleGraph.Metric
public import Coarse.Topology.MetricSpace.CoarselyGeodesic
public import Coarse.Topology.MetricSpace.QuasiIsometry

/-!
# Quasi-geodesics

A *`(c, b)`-quasi-geodesic* from `x` to `y` in a pseudometric space is a
`(c, b)`-quasi-isometric embedding `γ : [0, ℓ] → X` with `γ 0 = x` and `γ ℓ = y`; it need not be
continuous. A *`(c, b)`-quasi-geodesic space* is a space in which any two points are joined by a
`(c, b)`-quasi-geodesic; up to the constants, these are the coarsely geodesic spaces.

## Main definitions

* `Metric.IsQuasiGeodesicWith c b x y γ`: the map `γ : Set.Icc 0 ℓ → X` is a
  `(c, b)`-quasi-geodesic from `x` to `y`.
* `Metric.IsQuasiGeodesicSpaceWith X c b`: any two points of `X` are joined by a
  `(c, b)`-quasi-geodesic.
* `Metric.IsQuasiGeodesicSpace X`: `X` is a `(c, b)`-quasi-geodesic space for some `c` and `b`.

## Main statements

* `Metric.isQuasiIsometricEmbeddingWith_natFloor`: `t ↦ ⌊t⌋₊` from `[0, ℓ]` to `{0, …, ⌊ℓ⌋₊}` is a
  `(1, 1)`-quasi-isometric embedding.
* `Metric.IsQuasiGeodesicSpaceWith.isCoarselyGeodesicWith`: a `(c, b)`-quasi-geodesic space is
  `(c + b, c, c * b + 1)`-coarsely geodesic.
* `Metric.IsCoarselyGeodesicWith.isQuasiGeodesicSpaceWith`: an `(r, L, C)`-coarsely geodesic space
  is a `(max (max r L) 1, max r (C + 1))`-quasi-geodesic space.
* `Metric.isCoarselyGeodesic_iff_isQuasiGeodesicSpace`: the coarsely geodesic spaces are the
  quasi-geodesic spaces.

## Implementation notes

The domain of a quasi-geodesic is `[0, ℓ]` with `ℓ : ℝ≥0`, and the constants may be `0`. The
quasi-geodesics built from chains are step functions.

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

/-- A map `γ : [0, ℓ] → X` is a **`(c, b)`-quasi-geodesic** from `x` to `y` if it is a
`(c, b)`-quasi-isometric embedding with `γ 0 = x` and `γ ℓ = y`. It need not be continuous.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
structure IsQuasiGeodesicWith (c b : ℝ≥0) {ℓ : ℝ≥0} (x y : X) (γ : Set.Icc (0 : ℝ) ℓ → X) :
    Prop where
  /-- `γ` is a `(c, b)`-quasi-isometric embedding. -/
  isQuasiIsometricEmbeddingWith : IsQuasiIsometricEmbeddingWith c b γ
  /-- `γ` starts at `x`. -/
  apply_left : γ ⟨0, Set.left_mem_Icc.2 ℓ.coe_nonneg⟩ = x
  /-- `γ` ends at `y`. -/
  apply_right : γ ⟨ℓ, Set.right_mem_Icc.2 ℓ.coe_nonneg⟩ = y

/-- A pseudometric space is a **`(c, b)`-quasi-geodesic space** if any two points are joined by a
`(c, b)`-quasi-geodesic.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
def IsQuasiGeodesicSpaceWith (X : Type*) [PseudoMetricSpace X] (c b : ℝ≥0) : Prop :=
  ∀ x y : X, ∃ (ℓ : ℝ≥0) (γ : Set.Icc (0 : ℝ) ℓ → X), IsQuasiGeodesicWith c b x y γ

/-- A pseudometric space is a **quasi-geodesic space** if it is a `(c, b)`-quasi-geodesic space
for some constants `c` and `b`.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
def IsQuasiGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ c b, IsQuasiGeodesicSpaceWith X c b

/-- A `(c, b)`-quasi-geodesic space is `(c + b, c, c * b + 1)`-coarsely geodesic. -/
theorem IsQuasiGeodesicSpaceWith.isCoarselyGeodesicWith {c b : ℝ≥0}
    (h : IsQuasiGeodesicSpaceWith X c b) : IsCoarselyGeodesicWith X (c + b) c (c * b + 1) := by
  intro x y
  obtain ⟨ℓ, γ, hγ⟩ := h x y
  -- Sample `γ`, extended to `ℝ`, at parameters at most `1` apart.
  obtain ⟨p, hp⟩ := exists_ripsGraph_walk_of_dist_le (f := Set.IccExtend ℓ.coe_nonneg γ)
    (δ := 1) (c := c) (b := b) (r := c + b) ℓ.coe_nonneg one_pos (fun s hs t ht ↦ by
      rw [Set.IccExtend_of_mem _ _ hs, Set.IccExtend_of_mem _ _ ht]
      simpa [Subtype.dist_eq, Real.dist_eq] using
        hγ.isQuasiIsometricEmbeddingWith.coarseLipschitzWith ⟨s, hs⟩ ⟨t, ht⟩) (by simp)
  refine ⟨p.copy (by rw [Set.IccExtend_left, hγ.apply_left])
    (by rw [Set.IccExtend_right, hγ.apply_right]), ?_⟩
  -- The lower bound of `γ` at the endpoints gives `ℓ ≤ c * dist x y + c * b`.
  have hℓ := hγ.isQuasiIsometricEmbeddingWith.coarseAntilipschitzWith
    ⟨0, Set.left_mem_Icc.2 ℓ.coe_nonneg⟩ ⟨ℓ, Set.right_mem_Icc.2 ℓ.coe_nonneg⟩
  rw [hγ.apply_left, hγ.apply_right, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg ℓ.coe_nonneg, NNReal.coe_mul] at hℓ
  rw [SimpleGraph.Walk.length_copy, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one]
  rw [div_one] at hp
  linarith

/-- The map `t ↦ ⌊t⌋₊` from `[0, ℓ]` to `{0, …, ⌊ℓ⌋₊}` is a `(1, 1)`-quasi-isometric embedding:
it turns maps on `{0, …, ⌊ℓ⌋₊}` into step functions on `[0, ℓ]`. -/
theorem isQuasiIsometricEmbeddingWith_natFloor (ℓ : ℝ≥0) :
    IsQuasiIsometricEmbeddingWith 1 1 fun t : Set.Icc (0 : ℝ) ℓ ↦
      (⟨⌊(t : ℝ)⌋₊, Nat.floor_le_floor t.2.2⟩ : Set.Iic ⌊(ℓ : ℝ)⌋₊) := by
  -- `⌊s⌋₊ - ⌊t⌋₊` and `s - t` differ by less than `1`.
  refine ⟨fun s t ↦ ?_, fun s t ↦ ?_⟩ <;>
  · simp only [Subtype.dist_eq, Nat.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, mul_one]
    have := Nat.floor_le s.2.1
    have := Nat.floor_le t.2.1
    have := Nat.lt_floor_add_one (s : ℝ)
    have := Nat.lt_floor_add_one (t : ℝ)
    rw [abs_le]
    constructor <;> linarith [le_abs_self ((s : ℝ) - t), neg_abs_le ((s : ℝ) - t),
      le_abs_self ((⌊(s : ℝ)⌋₊ : ℝ) - ⌊(t : ℝ)⌋₊), neg_abs_le ((⌊(s : ℝ)⌋₊ : ℝ) - ⌊(t : ℝ)⌋₊)]

/-- An `(r, L, C)`-coarsely geodesic space is a `(max (max r L) 1, max r (C + 1))`-quasi-geodesic
space. -/
theorem IsCoarselyGeodesicWith.isQuasiGeodesicSpaceWith {r L C : ℝ≥0}
    (h : IsCoarselyGeodesicWith X r L C) :
    IsQuasiGeodesicSpaceWith X (max (max r L) 1) (max r (C + 1)) := by
  intro x y
  -- A shortest chain `x = x 0, …, x n = y`, indexed by `{0, …, n}`, is `r`-Lipschitz and
  -- `(L, C)`-coarse antilipschitz; precompose it with `t ↦ ⌊t⌋₊` on `[0, n]`.
  obtain ⟨q, -⟩ := h x y
  obtain ⟨p, hp⟩ := q.reachable.exists_walk_length_eq_dist
  set ℓ : ℝ≥0 := (p.length : ℝ≥0)
  have hℓ : ⌊(ℓ : ℝ)⌋₊ = p.length := by simp [ℓ]
  let f : Set.Iic ⌊(ℓ : ℝ)⌋₊ → X := fun i ↦ p.getVert i
  have hf (i j : Set.Iic ⌊(ℓ : ℝ)⌋₊) (hij : (i : ℕ) ≤ j) :
      dist (f i) (f j) ≤ r * dist i j ∧ dist i j ≤ L * dist (f i) (f j) + C := by
    have hj : (j : ℕ) ≤ p.length := hℓ ▸ j.2
    rw [Subtype.dist_eq, Nat.dist_eq, abs_sub_comm, abs_of_nonneg (by simpa using hij),
      ← Nat.cast_sub hij]
    obtain ⟨q, hq⟩ := h (f i) (f j)
    refine ⟨p.dist_getVert_le_mul (φ := id)
      (fun _ _ (hadj : (ripsGraph X r).Adj _ _) ↦ hadj.2) hij hj, ?_⟩
    rw [← p.dist_getVert_of_length_eq_dist hp hij hj]
    exact (Nat.cast_le.2 (SimpleGraph.dist_le q)).trans hq
  have hlip : CoarseLipschitzWith r 0 f := fun i j ↦ by
    rcases le_total (i : ℕ) j with hij | hij
    · simpa using (hf i j hij).1
    · simpa [dist_comm] using (hf j i hij).1
  have hanti : CoarseAntilipschitzWith L C f := fun i j ↦ by
    rcases le_total (i : ℕ) j with hij | hij
    · exact (hf i j hij).2
    · simpa [dist_comm] using (hf j i hij).2
  have hfl := isQuasiIsometricEmbeddingWith_natFloor ℓ
  refine ⟨ℓ, f ∘ fun t ↦ ⟨⌊(t : ℝ)⌋₊, Nat.floor_le_floor t.2.2⟩, ?_, by simp [f],
    by simp [f, ℓ]⟩
  simpa using (hanti.comp hfl.coarseAntilipschitzWith).isQuasiIsometricEmbeddingWith
    (hlip.comp hfl.coarseLipschitzWith)

/-- A pseudometric space is coarsely geodesic if and only if it is a quasi-geodesic space.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
theorem isCoarselyGeodesic_iff_isQuasiGeodesicSpace :
    IsCoarselyGeodesic X ↔ IsQuasiGeodesicSpace X :=
  ⟨fun ⟨_, _, _, h⟩ ↦ ⟨_, _, h.isQuasiGeodesicSpaceWith⟩,
   fun ⟨_, _, h⟩ ↦ ⟨_, _, _, h.isCoarselyGeodesicWith⟩⟩

end Metric
