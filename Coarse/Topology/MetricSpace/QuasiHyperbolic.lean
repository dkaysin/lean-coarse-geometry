/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Topology.MetricSpace.QuasiGeodesic

/-!
# Slim quasi-geodesic triangles

A *`(c, b)`-quasi-geodesic triangle* consists of three points and `(c, b)`-quasi-geodesic segments
between them, its sides. It is *`δ`-slim* if every point of each side is within distance `δ` of a
point of one of the other two sides. This is the condition behind Löh's quasi-hyperbolic spaces.

## Main definitions

* `Metric.HasSlimQuasiGeodesicTrianglesWith X c b δ`: every `(c, b)`-quasi-geodesic triangle in
  `X` is `δ`-slim.

## Implementation notes

As for `Metric.HasSlimTrianglesWith`, the condition is asked for the first side of every triangle
only; the other sides are the first sides of the rotated triangles. The constants `c` and `b` may
be `0`; a `(1, 0)`-quasi-geodesic is a geodesic.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Definition 7.2.5
* [M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
  Section III.H.1, before Corollary 1.8

## Tags

quasi-geodesic triangle, slim triangles, quasi-hyperbolic space, hyperbolic space
-/

@[expose] public section

open scoped NNReal

namespace Metric

/-- A pseudometric space has **`δ`-slim `(c, b)`-quasi-geodesic triangles** if for every
`(c, b)`-quasi-geodesic triangle, every point of one side is within distance `δ` of a point of one
of the other two sides.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 7.2.5. -/
def HasSlimQuasiGeodesicTrianglesWith (X : Type*) [PseudoMetricSpace X] (c b : ℝ≥0) (δ : ℝ) :
    Prop :=
  ∀ ⦃x y z : X⦄ ⦃s₁ s₂ s₃ : Set X⦄,
    IsQuasiGeodesicSegmentWith c b s₁ x y →
    IsQuasiGeodesicSegmentWith c b s₂ y z →
    IsQuasiGeodesicSegmentWith c b s₃ z x →
    ∀ p ∈ s₁, ∃ q ∈ s₂ ∪ s₃, dist p q ≤ δ

end Metric
