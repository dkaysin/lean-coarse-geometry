/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Topology.MetricSpace.CoarseLipschitz
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Coarsely connected and coarsely geodesic spaces

An *`r`-chain* from `x` to `y` in a pseudometric space is a finite sequence of points from `x` to
`y` in which consecutive points are at distance at most `r`. A space is *`r`-coarsely connected* if
it is nonempty and any two points are joined by an `r`-chain, and *`(r, L, C)`-coarsely geodesic*
if any two points `x` and `y` are joined by an `r`-chain with at most `L * dist x y + C` steps.

## Main definitions

* `Metric.ripsGraph X r`: the simple graph on `X` in which distinct points at distance at most `r`
  are adjacent.
* `Metric.IsCoarselyConnectedWith X r`: `X` is nonempty and any two of its points are joined by an
  `r`-chain.
* `Metric.IsCoarselyGeodesicWith X r L C`: any two points `x`, `y` of `X` are joined by an
  `r`-chain with at most `L * dist x y + C` steps.
* `Metric.IsCoarselyConnected X`, `Metric.IsCoarselyGeodesic X`: the same for some constants.

## Main statements

* `SimpleGraph.Walk.dist_le_mul_length`: a map from the vertices of a graph into a pseudometric
  space that moves adjacent vertices by at most `K` moves the endpoints of a walk by at most `K`
  times its length.
* `SimpleGraph.Walk.dist_getVert_le_mul`: the same for the vertices at positions `i ≤ j` of a walk,
  with `j - i` in place of the length.
* `Metric.exists_ripsGraph_walk_length_le`: a sequence of points whose first `n` steps have length
  at most `r` gives an `r`-chain with at most `n` steps.
* `Metric.IsCoarselyGeodesicWith.coarseLipschitzWith`: on an `(r, L, C)`-coarsely geodesic space, a
  map that moves points at distance at most `r` by at most `A` is `(A * L, A * C)`-coarse
  Lipschitz.
* `NormedSpace.isCoarselyGeodesicWith`: a real normed space is `(r, r⁻¹, 1)`-coarsely geodesic for
  every `r > 0`.

## Implementation notes

An `r`-chain is a walk in `Metric.ripsGraph X r`, and its number of steps is the length of the
walk. A walk does not repeat a point in consecutive steps; dropping such repetitions only shortens
a chain.

## References

* [C. Druțu, M. Kapovich, *Geometric Group Theory*][drutu2018], Lemma 8.8

## Tags

coarsely geodesic, coarsely connected, chain, Rips graph, quasi-geodesic, coarse geometry
-/

@[expose] public section

open scoped NNReal

/-- If `φ` moves adjacent vertices of `G` by at most `K`, then it moves the endpoints of a walk
by at most `K` times the length of the walk. -/
theorem SimpleGraph.Walk.dist_le_mul_length {V X : Type*} [PseudoMetricSpace X]
    {G : SimpleGraph V} {φ : V → X} {K : ℝ} (hφ : ∀ u v, G.Adj u v → Dist.dist (φ u) (φ v) ≤ K)
    {u v : V} (p : G.Walk u v) : Dist.dist (φ u) (φ v) ≤ K * p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    grw [dist_triangle _ (φ _), hφ _ _ h, ih]
    rw [length_cons, Nat.cast_succ]
    linarith

/-- If `φ` moves adjacent vertices of `G` by at most `K`, then it moves the vertices at positions
`i ≤ j ≤ p.length` of a walk `p` by at most `K * (j - i)`. -/
theorem SimpleGraph.Walk.dist_getVert_le_mul {V X : Type*} [PseudoMetricSpace X]
    {G : SimpleGraph V} {φ : V → X} {K : ℝ} (hφ : ∀ u v, G.Adj u v → Dist.dist (φ u) (φ v) ≤ K)
    {u v : V} (p : G.Walk u v) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    Dist.dist (φ (p.getVert i)) (φ (p.getVert j)) ≤ K * (j - i : ℕ) := by
  -- Apply `dist_le_mul_length` to the subwalk from position `i` to position `j`.
  have h := ((p.drop i).take (j - i)).dist_le_mul_length hφ
  rwa [take_length, drop_length, drop_getVert, Nat.add_sub_cancel' hij,
    min_eq_left (by omega)] at h

namespace Metric

/-- The **Rips graph** of a pseudometric space at scale `r`: distinct points are adjacent if they
are at distance at most `r`. -/
def ripsGraph (X : Type*) [PseudoMetricSpace X] (r : ℝ≥0) : SimpleGraph X where
  Adj x y := x ≠ y ∧ dist x y ≤ r
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, (dist_comm (α := X) _ _).trans_le h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- A sequence of points in which the first `n` steps have length at most `r` gives an `r`-chain
from its `0`-th to its `n`-th point with at most `n` steps. -/
theorem exists_ripsGraph_walk_length_le {X : Type*} [PseudoMetricSpace X] {r : ℝ≥0} (f : ℕ → X)
    (n : ℕ) (hf : ∀ k < n, dist (f k) (f (k + 1)) ≤ r) :
    ∃ p : (ripsGraph X r).Walk (f 0) (f n), p.length ≤ n := by
  induction n with
  | zero => exact ⟨.nil, le_rfl⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih fun k hk ↦ hf k (by omega)
    by_cases h : f n = f (n + 1)
    · exact ⟨p.copy rfl h, by simp; omega⟩
    · have hadj : (ripsGraph X r).Adj (f n) (f (n + 1)) := ⟨h, hf n n.lt_succ_self⟩
      exact ⟨p.concat hadj, by simp; omega⟩

/-- A pseudometric space is **`r`-coarsely connected** if it is nonempty and any two points are
joined by a chain of points in which consecutive points are at distance at most `r`. -/
def IsCoarselyConnectedWith (X : Type*) [PseudoMetricSpace X] (r : ℝ≥0) : Prop :=
  (ripsGraph X r).Connected

/-- A pseudometric space is **`(r, L, C)`-coarsely geodesic** if any two points `x` and `y` are
joined by a chain with consecutive points at distance at most `r` and with at most
`L * dist x y + C` steps. -/
def IsCoarselyGeodesicWith (X : Type*) [PseudoMetricSpace X] (r L C : ℝ≥0) : Prop :=
  ∀ x y : X, ∃ p : (ripsGraph X r).Walk x y, (p.length : ℝ) ≤ L * dist x y + C

/-- A pseudometric space is **coarsely connected** if it is `r`-coarsely connected for some
`r`. -/
def IsCoarselyConnected (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ r, IsCoarselyConnectedWith X r

/-- A pseudometric space is **coarsely geodesic** if it is `(r, L, C)`-coarsely geodesic for some
constants `r`, `L` and `C`. -/
def IsCoarselyGeodesic (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ r L C, IsCoarselyGeodesicWith X r L C

/-- A nonempty `(r, L, C)`-coarsely geodesic space is `r`-coarsely connected. -/
theorem IsCoarselyGeodesicWith.isCoarselyConnectedWith {X : Type*} [PseudoMetricSpace X]
    [Nonempty X] {r L C : ℝ≥0} (h : IsCoarselyGeodesicWith X r L C) :
    IsCoarselyConnectedWith X r :=
  .mk fun x y ↦ ⟨(h x y).choose⟩

/-- On an `(r, L, C)`-coarsely geodesic space, a map that moves points at distance at most `r` by
at most `A` is `(A * L, A * C)`-coarse Lipschitz.

[C. Druțu, M. Kapovich, *Geometric Group Theory*][drutu2018], Lemma 8.8,
for geodesic spaces. -/
theorem IsCoarselyGeodesicWith.coarseLipschitzWith {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {r L C A : ℝ≥0} (hX : IsCoarselyGeodesicWith X r L C) {f : X → Y}
    (hf : ∀ x y, dist x y ≤ r → dist (f x) (f y) ≤ A) : CoarseLipschitzWith (A * L) (A * C) f := by
  intro x y
  -- Follow a chain from `x` to `y` with at most `L * dist x y + C` steps.
  obtain ⟨p, hp⟩ := hX x y
  calc dist (f x) (f y) ≤ A * p.length :=
        p.dist_le_mul_length fun u v (h : (ripsGraph X r).Adj u v) ↦ hf u v h.2
    _ ≤ A * (L * dist x y + C) := by gcongr
    _ = A * L * dist x y + A * C := by ring

end Metric

/-- A real normed space is `(r, r⁻¹, 1)`-coarsely geodesic for every `r > 0`. -/
theorem NormedSpace.isCoarselyGeodesicWith {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ≥0} (hr : 0 < r) : Metric.IsCoarselyGeodesicWith E r r⁻¹ 1 := by
  intro x y
  -- Cut the segment from `x` to `y` into `m ≥ ‖x - y‖ / r` steps of equal length.
  set m := max ⌈‖x - y‖ / r⌉₊ 1
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hstep (k : ℕ) (_ : k < m) :
      dist (x + ((k : ℝ) / m) • (y - x)) (x + (((k + 1 : ℕ) : ℝ) / m) • (y - x)) ≤ r := by
    have hlen : ‖x - y‖ ≤ m * r := by
      rw [← div_le_iff₀ (by exact_mod_cast hr)]
      exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, norm_sub_rev y x,
      Nat.cast_succ, ← sub_div, abs_div, abs_of_pos hm, sub_add_cancel_left, abs_neg, abs_one,
      div_mul_eq_mul_div, one_mul, div_le_iff₀ hm, mul_comm]
    exact hlen
  obtain ⟨p, hp⟩ := Metric.exists_ripsGraph_walk_length_le _ m hstep
  refine ⟨p.copy (by simp) (by simp [hm.ne']), ?_⟩
  -- The number of steps is `m ≤ ‖x - y‖ / r + 1`.
  have hm' : (m : ℝ) ≤ ‖x - y‖ / r + 1 := by
    rcases max_choice ⌈‖x - y‖ / r⌉₊ 1 with h | h <;> rw [show m = _ from h]
    · exact (Nat.ceil_lt_add_one (by positivity)).le
    · simp only [Nat.cast_one, le_add_iff_nonneg_left]
      positivity
  rw [SimpleGraph.Walk.length_copy, dist_eq_norm, NNReal.coe_one, NNReal.coe_inv,
    inv_mul_eq_div]
  exact (Nat.cast_le.2 hp).trans hm'
