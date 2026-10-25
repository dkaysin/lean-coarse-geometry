/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Geodesics and geodesic spaces

A *geodesic* from `x` to `y` in a pseudometric space is an isometric map from the interval
`[0, dist x y]` sending `0` to `x` and `dist x y` to `y`. A space is *geodesic* if any two points
are joined by a geodesic.

## Main definitions

* `Metric.IsGeodesic x y γ`: the map `γ : Set.Icc 0 (dist x y) → X` is a geodesic from `x` to `y`.
* `Metric.IsGeodesicSpace X`: any two points of `X` are joined by a geodesic.

## Implementation notes

The interval of a geodesic from `x` to `y` is `Set.Icc 0 (dist x y)`, since an isometric map from
`[0, ℓ]` with these endpoints forces `ℓ = dist x y`. Geodesics are not required to be injective,
which matters only in pseudometric spaces.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Definition 5.3.1
* [M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
  Definition I.1.3

## Tags

geodesic, geodesic segment, geodesic space, metric space
-/

@[expose] public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A map `γ : [0, dist x y] → X` is a **geodesic** from `x` to `y` if it is an isometry with
`γ 0 = x` and `γ (dist x y) = y`. -/
structure IsGeodesic (x y : X) (γ : Set.Icc (0 : ℝ) (dist x y) → X) : Prop where
  isometry : Isometry γ
  apply_left : γ ⟨0, Set.left_mem_Icc.2 dist_nonneg⟩ = x
  apply_right : γ ⟨dist x y, Set.right_mem_Icc.2 dist_nonneg⟩ = y

/-- A pseudometric space is **geodesic** if any two points are joined by a geodesic. -/
def IsGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsGeodesic x y γ

end Metric
