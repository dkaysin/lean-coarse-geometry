/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Coarsely connected and coarsely geodesic spaces

An *`r`-chain* from `x` to `y` in a pseudometric space is a finite sequence of points from `x` to
`y` in which consecutive points are at distance at most `r`. A space is *`r`-coarsely connected* if
any two points are joined by an `r`-chain, and *`(r, L, C)`-coarsely geodesic* if any two points
`x` and `y` are joined by an `r`-chain with at most `L * dist x y + C` steps.

## Main definitions

* `Metric.IsCoarselyConnectedWith X r`: any two points of `X` are joined by an `r`-chain.
* `Metric.IsCoarselyGeodesicWith X r L C`: any two points `x`, `y` of `X` are joined by an
  `r`-chain with at most `L * dist x y + C` steps.

## Main statements

* `NormedSpace.isCoarselyGeodesicWith`: a real normed space is `(r, r⁻¹, 1)`-coarsely geodesic for
  every `r > 0`.

## Implementation notes

A coarsely connected space is described with `Relation.ReflTransGen`, since no count of steps is
needed. A chain with a count is a map `p : Fin (n + 1) → X` with `n` steps.

## Tags

coarsely geodesic, coarsely connected, chain, quasi-geodesic, coarse geometry
-/

@[expose] public section

open scoped NNReal

namespace Metric

/-- A pseudometric space is **`r`-coarsely connected** if any two points are joined by a chain
of points in which consecutive points are at distance at most `r`. -/
def IsCoarselyConnectedWith (X : Type*) [PseudoMetricSpace X] (r : ℝ≥0) : Prop :=
  ∀ x y : X, Relation.ReflTransGen (fun a b : X ↦ dist a b ≤ r) x y

/-- A pseudometric space is **`(r, L, C)`-coarsely geodesic** if any two points `x` and `y` are
joined by a chain `p 0 = x, …, p n = y` with consecutive points at distance at most `r` and with
at most `L * dist x y + C` steps. -/
def IsCoarselyGeodesicWith (X : Type*) [PseudoMetricSpace X] (r L C : ℝ≥0) : Prop :=
  ∀ x y : X, ∃ (n : ℕ) (p : Fin (n + 1) → X), p 0 = x ∧ p (Fin.last n) = y ∧
    (∀ i : Fin n, dist (p i.castSucc) (p i.succ) ≤ r) ∧ (n : ℝ) ≤ L * dist x y + C

end Metric

/-- A real normed space is `(r, r⁻¹, 1)`-coarsely geodesic for every `r > 0`. -/
theorem NormedSpace.isCoarselyGeodesicWith {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ≥0} (hr : 0 < r) : Metric.IsCoarselyGeodesicWith E r r⁻¹ 1 :=
  sorry
