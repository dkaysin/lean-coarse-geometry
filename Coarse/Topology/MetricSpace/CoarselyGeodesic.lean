/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Coarsely connected and coarsely geodesic spaces

An *`r`-chain* from `x` to `y` in a pseudometric space is a finite sequence of points from `x` to
`y` in which consecutive points are at distance at most `r`. A space is *`r`-coarsely connected* if
any two points are joined by an `r`-chain, and *`(r, L, C)`-coarsely geodesic* if any two points
`x` and `y` are joined by an `r`-chain with at most `L * dist x y + C` steps.

## Main definitions

* `Metric.ripsGraph X r`: the simple graph on `X` in which distinct points at distance at most `r`
  are adjacent.
* `Metric.IsCoarselyConnectedWith X r`: any two points of `X` are joined by an `r`-chain.
* `Metric.IsCoarselyGeodesicWith X r L C`: any two points `x`, `y` of `X` are joined by an
  `r`-chain with at most `L * dist x y + C` steps.
* `Metric.IsCoarselyConnected X`, `Metric.IsCoarselyGeodesic X`: the same for some constants.

## Main statements

* `SimpleGraph.Walk.dist_le_mul_length`: a map from the vertices of a graph into a pseudometric
  space that moves adjacent vertices by at most `K` moves the endpoints of a walk by at most `K`
  times its length.
* `NormedSpace.isCoarselyGeodesicWith`: a real normed space is `(r, r⁻¹, 1)`-coarsely geodesic for
  every `r > 0`.

## Implementation notes

An `r`-chain is a walk in `Metric.ripsGraph X r`, and its number of steps is the length of the
walk. A walk does not repeat a point in consecutive steps; dropping such repetitions only shortens
a chain.

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

namespace Metric

/-- The **Rips graph** of a pseudometric space at scale `r`: distinct points are adjacent if they
are at distance at most `r`. -/
def ripsGraph (X : Type*) [PseudoMetricSpace X] (r : ℝ≥0) : SimpleGraph X where
  Adj x y := x ≠ y ∧ dist x y ≤ r
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, (dist_comm (α := X) _ _).trans_le h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- A pseudometric space is **`r`-coarsely connected** if any two points are joined by a chain
of points in which consecutive points are at distance at most `r`. -/
def IsCoarselyConnectedWith (X : Type*) [PseudoMetricSpace X] (r : ℝ≥0) : Prop :=
  (ripsGraph X r).Preconnected

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

end Metric

/-- A real normed space is `(r, r⁻¹, 1)`-coarsely geodesic for every `r > 0`. -/
theorem NormedSpace.isCoarselyGeodesicWith {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ≥0} (hr : 0 < r) : Metric.IsCoarselyGeodesicWith E r r⁻¹ 1 :=
  sorry
