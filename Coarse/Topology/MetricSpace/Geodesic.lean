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
by a geodesic. A *geodesic segment* from `x` to `x'` is the image of a geodesic from `x` to `x'`.

## Main definitions

* `Metric.IsGeodesic γ t t' x x'`: the map `γ : ℝ → X` is a geodesic on `[t, t']` from `x` to `x'`.
* `Metric.IsGeodesicSegment s x x'`: the set `s` is the image of a geodesic from `x` to `x'`.
* `Metric.IsGeodesicSpace X`: any two points of `X` are joined by a geodesic.

## Implementation notes

A geodesic is a map `γ : ℝ → X` of which only the values on `[t, t']` matter, as for Mathlib's
`Manifold.pathELength`: this avoids subtypes of `ℝ`. The isometry on `[t, t']` forces
`t' - t = dist x x'`. Geodesics are not required to be injective, which matters only in
pseudometric spaces. Where only the points of a geodesic matter, as for the sides of a triangle,
statements use `Metric.IsGeodesicSegment` and leave out the parametrisation.

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

/-- A map `γ : ℝ → X` is a **geodesic** on `[t, t']` from `x` to `x'` if it is isometric on
`[t, t']`, with `γ t = x` and `γ t' = x'`. -/
structure IsGeodesic (γ : ℝ → X) (t t' : ℝ) (x x' : X) : Prop where
  le : t ≤ t'
  apply_left : γ t = x
  apply_right : γ t' = x'
  dist_eq : ∀ s ∈ Set.Icc t t', ∀ s' ∈ Set.Icc t t', dist (γ s) (γ s') = |s - s'|

/-- A set `s` is a **geodesic segment** from `x` to `x'` if it is the image of a geodesic from `x`
to `x'`. -/
def IsGeodesicSegment (s : Set X) (x x' : X) : Prop :=
  ∃ (γ : ℝ → X) (t t' : ℝ), IsGeodesic γ t t' x x' ∧ γ '' Set.Icc t t' = s

/-- A pseudometric space is **geodesic** if any two points are joined by a geodesic. -/
def IsGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x x' : X, ∃ (γ : ℝ → X) (t t' : ℝ), IsGeodesic γ t t' x x'

end Metric
