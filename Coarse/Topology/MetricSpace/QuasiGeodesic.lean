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

/-!
# Quasi-geodesics

A *`(c, b)`-quasi-geodesic* from `x` to `x'` in a pseudometric space is a
`(c, b)`-quasi-isometric embedding `γ : [t, t'] → X` with `γ t = x` and `γ t' = x'`; it need not
be continuous. A *`(c, b)`-quasi-geodesic space* is a space in which any two points are joined by a
`(c, b)`-quasi-geodesic; up to the constants, these are the coarsely geodesic spaces.

## Main definitions

* `Metric.QuasiGeodesic c b x x'`: a `(c, b)`-quasi-geodesic from `x` to `x'`, bundled with its
  interval `[t, t']`.
* `Metric.IsQuasiGeodesicSpaceWith X c b`: any two points of `X` are joined by a
  `(c, b)`-quasi-geodesic.
* `Metric.IsQuasiGeodesicSpace X`: `X` is a `(c, b)`-quasi-geodesic space for some `c` and `b`.

## Main statements

* `Metric.Geodesic.toQuasiGeodesic`: a geodesic is a `(1, 0)`-quasi-geodesic.
* `Metric.QuasiGeodesic.nonempty_coarseGeodesic`: a `(c, b)`-quasi-geodesic from `x` to `x'`
  gives an `(r, c / δ, c * b / δ + 1)`-coarse geodesic from `x` to `x'` if `c * δ + b ≤ r`.
* `Metric.IsGeodesicSpace.isCoarselyGeodesicSpaceWith`: a geodesic space is `(r, r⁻¹, 1)`-coarsely
  geodesic for every `r > 0`.
* `Metric.isQuasiIsometricEmbeddingWith_natFloor`: `t ↦ ⌊t⌋₊` from `[0, ℓ]` to `{0, …, ⌊ℓ⌋₊}` is a
  `(1, 1)`-quasi-isometric embedding.
* `Metric.IsQuasiGeodesicSpaceWith.isCoarselyGeodesicSpaceWith`: a `(c, b)`-quasi-geodesic space is
  `(c + b, c, c * b + 1)`-coarsely geodesic.
* `Metric.IsCoarselyGeodesicSpaceWith.isQuasiGeodesicSpaceWith`: an `(r, L, C)`-coarsely geodesic
  space is a `(max (max r L) 1, max r (C + 1))`-quasi-geodesic space.
* `Metric.isCoarselyGeodesicSpace_iff_isQuasiGeodesicSpace`: the coarsely geodesic spaces are the
  quasi-geodesic spaces.

## Implementation notes

A quasi-geodesic bundles its endpoints `t ≤ t'` with the map, as `Metric.Geodesic` does, and
coerces to a function through `CoeFun`. The constants may be `0`. The quasi-geodesics built from
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

/-- A **`(c, b)`-quasi-geodesic** from `x` to `x'` is a `(c, b)`-quasi-isometric embedding
`γ : [t, t'] → X` with `γ t = x` and `γ t' = x'`. It need not be continuous.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
structure QuasiGeodesic (c b : ℝ≥0) (x x' : X) where
  t : ℝ
  t' : ℝ
  le : t ≤ t'
  toFun : Set.Icc t t' → X
  isQuasiIsometricEmbeddingWith : IsQuasiIsometricEmbeddingWith c b toFun
  apply_left : toFun ⟨t, Set.left_mem_Icc.2 le⟩ = x
  apply_right : toFun ⟨t', Set.right_mem_Icc.2 le⟩ = x'

attribute [coe] QuasiGeodesic.toFun

instance {c b : ℝ≥0} {x x' : X} :
    CoeFun (QuasiGeodesic c b x x') fun γ ↦ Set.Icc γ.t γ.t' → X :=
  ⟨QuasiGeodesic.toFun⟩

/-- A pseudometric space is a **`(c, b)`-quasi-geodesic space** if any two points are joined by a
`(c, b)`-quasi-geodesic.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
def IsQuasiGeodesicSpaceWith (X : Type*) [PseudoMetricSpace X] (c b : ℝ≥0) : Prop :=
  ∀ x x' : X, Nonempty (QuasiGeodesic c b x x')

/-- A pseudometric space is a **quasi-geodesic space** if it is a `(c, b)`-quasi-geodesic space
for some constants `c` and `b`.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
def IsQuasiGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ c b, IsQuasiGeodesicSpaceWith X c b

/-- A geodesic is a `(1, 0)`-quasi-geodesic. -/
def Geodesic.toQuasiGeodesic {x x' : X} (γ : Geodesic x x') : QuasiGeodesic 1 0 x x' where
  t := γ.t
  t' := γ.t'
  toFun := γ
  isQuasiIsometricEmbeddingWith := ⟨γ.isometry.lipschitzWith.coarseLipschitzWith,
    by simpa using γ.isometry.antilipschitzWith.coarseAntilipschitzWith⟩
  le := γ.le
  apply_left := γ.apply_left
  apply_right := γ.apply_right

/-- A `(c, b)`-quasi-geodesic from `x` to `x'`, sampled at parameters at most `δ` apart, gives a
`(r, c / δ, c * b / δ + 1)`-coarse geodesic from `x` to `x'`, if `c * δ + b ≤ r`. -/
theorem QuasiGeodesic.nonempty_coarseGeodesic {c b r δ : ℝ≥0} {x x' : X}
    (γ : QuasiGeodesic c b x x') (hδ : 0 < δ) (hr : c * δ + b ≤ r) :
    Nonempty (CoarseGeodesic r (c / δ) (c * b / δ + 1) x x') := by
  obtain ⟨t, t', hle, γ, hγ, hleft, hright⟩ := γ
  have hδ' : (0 : ℝ) < δ := NNReal.coe_pos.2 hδ
  -- The lower bound of `γ` at the endpoints gives `t' - t ≤ c * dist x x' + c * b`.
  have hℓ' := hγ.coarseAntilipschitzWith ⟨t, Set.left_mem_Icc.2 hle⟩ ⟨t', Set.right_mem_Icc.2 hle⟩
  rw [hleft, hright, Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle),
    NNReal.coe_mul] at hℓ'
  -- Cut `[t, t']` into `m ≥ (t' - t) / δ` steps of equal length.
  set m := max ⌈(t' - t) / δ⌉₊ 1
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hℓ : 0 ≤ t' - t := sub_nonneg.2 hle
  have hmem (k : ℕ) (hk : k ≤ m) : t + (k : ℝ) / m * (t' - t) ∈ Set.Icc t t' := by
    have : (k : ℝ) / m * (t' - t) ≤ t' - t :=
      mul_le_of_le_one_left hℓ ((div_le_one hm).2 (by exact_mod_cast hk))
    exact ⟨le_add_of_nonneg_right (by positivity), by linarith⟩
  have hstep (k : ℕ) (hk : k < m) :
      dist (Set.IccExtend hle γ (t + (k : ℝ) / m * (t' - t)))
        (Set.IccExtend hle γ (t + ((k + 1 : ℕ) : ℝ) / m * (t' - t))) ≤ r := by
    have hlen : (t' - t) / m ≤ δ := by
      rw [div_le_iff₀ hm, ← div_le_iff₀' hδ']
      exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
    have habs : |t + (k : ℝ) / m * (t' - t) - (t + ((k + 1 : ℕ) : ℝ) / m * (t' - t))| =
        (t' - t) / m := by
      rw [add_sub_add_left_eq_sub, ← sub_mul, Nat.cast_succ, ← sub_div, sub_add_cancel_left,
        abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hm, abs_of_nonneg hℓ, one_div_mul_eq_div]
    rw [Set.IccExtend_of_mem _ _ (hmem k hk.le), Set.IccExtend_of_mem _ _ (hmem (k + 1) hk)]
    calc dist _ _ ≤ c * dist (⟨_, hmem k hk.le⟩ : Set.Icc t t') ⟨_, hmem (k + 1) hk⟩ + b :=
          hγ.coarseLipschitzWith _ _
      _ = c * ((t' - t) / m) + b := by rw [Subtype.dist_eq, Real.dist_eq, habs]
      _ ≤ c * δ + b := by gcongr
      _ ≤ r := by exact_mod_cast hr
  obtain ⟨p, hp⟩ := exists_ripsGraph_walk_length_le _ m hstep
  refine ⟨⟨p.copy (by simpa using hleft) (by simpa [hm.ne'] using hright), ?_⟩⟩
  -- The number of steps is `m ≤ (t' - t) / δ + 1 ≤ (c * dist x x' + c * b) / δ + 1`.
  have hm' : (m : ℝ) ≤ (t' - t) / δ + 1 := by
    rcases max_choice ⌈(t' - t) / δ⌉₊ 1 with h | h <;> rw [show m = _ from h]
    · exact (Nat.ceil_lt_add_one (by positivity)).le
    · simp only [Nat.cast_one, le_add_iff_nonneg_left]
      positivity
  rw [SimpleGraph.Walk.length_copy]
  calc (p.length : ℝ) ≤ m := Nat.cast_le.2 hp
    _ ≤ (t' - t) / δ + 1 := hm'
    _ ≤ (c * dist x x' + c * b) / δ + 1 := by gcongr
    _ = ↑(c / δ) * dist x x' + ↑(c * b / δ + 1) := by push_cast; ring

/-- A `(c, b)`-quasi-geodesic space is `(c + b, c, c * b + 1)`-coarsely geodesic. -/
theorem IsQuasiGeodesicSpaceWith.isCoarselyGeodesicSpaceWith {c b : ℝ≥0}
    (h : IsQuasiGeodesicSpaceWith X c b) : IsCoarselyGeodesicSpaceWith X (c + b) c (c * b + 1) :=
  fun x x' ↦ by
    -- Sample a quasi-geodesic at parameters at most `1` apart.
    simpa using (h x x').some.nonempty_coarseGeodesic one_pos (by simp)

/-- A geodesic space is `(r, r⁻¹, 1)`-coarsely geodesic for every `r > 0`. -/
theorem IsGeodesicSpace.isCoarselyGeodesicSpaceWith (hX : IsGeodesicSpace X) {r : ℝ≥0}
    (hr : 0 < r) : IsCoarselyGeodesicSpaceWith X r r⁻¹ 1 :=
  fun x x' ↦ by
    -- Sample a geodesic at parameters at most `r` apart.
    simpa using (hX x x').some.toQuasiGeodesic.nonempty_coarseGeodesic hr (by simp)

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
theorem IsCoarselyGeodesicSpaceWith.isQuasiGeodesicSpaceWith {r L C : ℝ≥0}
    (h : IsCoarselyGeodesicSpaceWith X r L C) :
    IsQuasiGeodesicSpaceWith X (max (max r L) 1) (max r (C + 1)) := by
  intro x x'
  -- A shortest chain from `x` to `x'`, indexed by `{0, …, n}`, is `r`-Lipschitz and
  -- `(L, C)`-coarse antilipschitz; precompose it with `t ↦ ⌊t⌋₊` on `[0, n]`.
  obtain ⟨⟨q, -⟩⟩ := h x x'
  obtain ⟨p, hp⟩ := q.reachable.exists_walk_length_eq_dist
  set t : ℝ≥0 := (p.length : ℝ≥0)
  have ht : ⌊(t : ℝ)⌋₊ = p.length := by simp [t]
  let f : Set.Iic ⌊(t : ℝ)⌋₊ → X := fun i ↦ p.getVert i
  have hf (i j : Set.Iic ⌊(t : ℝ)⌋₊) (hij : (i : ℕ) ≤ j) :
      dist (f i) (f j) ≤ r * dist i j ∧ dist i j ≤ L * dist (f i) (f j) + C := by
    have hj : (j : ℕ) ≤ p.length := ht ▸ j.2
    rw [Subtype.dist_eq, Nat.dist_eq, abs_sub_comm, abs_of_nonneg (by simpa using hij),
      ← Nat.cast_sub hij]
    obtain ⟨⟨q, hq⟩⟩ := h (f i) (f j)
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
  have hfl := isQuasiIsometricEmbeddingWith_natFloor t
  refine ⟨⟨0, t, t.coe_nonneg, f ∘ fun t ↦ ⟨⌊(t : ℝ)⌋₊, Nat.floor_le_floor t.2.2⟩, ?_,
    by simp [f], by simp [f, t]⟩⟩
  simpa using (hanti.comp hfl.coarseAntilipschitzWith).isQuasiIsometricEmbeddingWith
    (hlip.comp hfl.coarseLipschitzWith)

/-- A pseudometric space is coarsely geodesic if and only if it is a quasi-geodesic space.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.3.4. -/
theorem isCoarselyGeodesicSpace_iff_isQuasiGeodesicSpace :
    IsCoarselyGeodesicSpace X ↔ IsQuasiGeodesicSpace X :=
  ⟨fun ⟨_, _, _, h⟩ ↦ ⟨_, _, h.isQuasiGeodesicSpaceWith⟩,
   fun ⟨_, _, h⟩ ↦ ⟨_, _, _, h.isCoarselyGeodesicSpaceWith⟩⟩

end Metric
