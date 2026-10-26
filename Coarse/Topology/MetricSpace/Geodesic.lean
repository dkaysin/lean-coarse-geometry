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

A *geodesic* from `x` to `x'` in a pseudometric space is an isometric map from an interval
`[t, t']` sending `t` to `x` and `t'` to `x'`. A space is *geodesic* if any two points are joined
by a geodesic.

## Main definitions

* `Metric.Geodesic x x'`: a geodesic from `x` to `x'`, bundled with its interval `[t, t']`.
* `Metric.IsGeodesicSpace X`: any two points of `X` are joined by a geodesic.

## Implementation notes

A geodesic bundles its endpoints `t ≤ t'` with the map `γ : Set.Icc t t' → X`; the isometry forces
`t' - t = dist x x'`. Since the domain depends on the geodesic, it coerces to a function through
`CoeFun` rather than `FunLike`. Geodesics are not required to be injective, which matters only in
pseudometric spaces.

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

/-- A **geodesic** from `x` to `x'` is an isometric map `γ : [t, t'] → X` with `γ t = x` and
`γ t' = x'`. -/
structure Geodesic (x x' : X) where
  t : ℝ
  t' : ℝ
  le : t ≤ t'
  toFun : Set.Icc t t' → X
  isometry : Isometry toFun
  apply_left : toFun ⟨t, Set.left_mem_Icc.2 le⟩ = x
  apply_right : toFun ⟨t', Set.right_mem_Icc.2 le⟩ = x'

attribute [coe] Geodesic.toFun

instance {x x' : X} : CoeFun (Geodesic x x') fun γ ↦ Set.Icc γ.t γ.t' → X :=
  ⟨Geodesic.toFun⟩

/-- A pseudometric space is **geodesic** if any two points are joined by a geodesic. -/
def IsGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x x' : X, Nonempty (Geodesic x x')

end Metric
