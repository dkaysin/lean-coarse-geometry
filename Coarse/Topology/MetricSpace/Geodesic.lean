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

* `Metric.IsGeodesic x x' γ`: the map `γ : Set.Icc t t' → X` is a geodesic from `x` to `x'`.
* `Metric.IsGeodesicSpace X`: any two points of `X` are joined by a geodesic.

## Implementation notes

The interval `[t, t']` of a geodesic from `x` to `x'` is arbitrary, with `t ≤ t'` as a field; the
isometry forces `t' - t = dist x x'`. Geodesics are not required to be injective, which matters
only in pseudometric spaces.

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

/-- A map `γ : [t, t'] → X` is a **geodesic** from `x` to `x'` if it is an isometry with
`γ t = x` and `γ t' = x'`. -/
structure IsGeodesic {t t' : ℝ} (x x' : X) (γ : Set.Icc t t' → X) : Prop where
  isometry : Isometry γ
  le : t ≤ t'
  apply_left : γ ⟨t, Set.left_mem_Icc.2 le⟩ = x
  apply_right : γ ⟨t', Set.right_mem_Icc.2 le⟩ = x'

/-- A pseudometric space is **geodesic** if any two points are joined by a geodesic. -/
def IsGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x x' : X, ∃ (t t' : ℝ) (γ : Set.Icc t t' → X), IsGeodesic x x' γ

end Metric
