/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Topology.MetricSpace.Geodesic
public import Coarse.Topology.MetricSpace.Hyperbolic

/-!
# Slim triangles

A *geodesic triangle* in a pseudometric space consists of three points and geodesic segments
between them, its sides. It is *`δ`-slim* if every point of each side is within distance `δ` of a
point of one of the other two sides. On geodesic spaces, having `δ`-slim triangles for some `δ` is
equivalent to the four-point condition `Metric.IsHyperbolic`.

## Main definitions

* `Metric.HasSlimTrianglesWith X δ`: every geodesic triangle in `X` is `δ`-slim.

## Main statements

* `Metric.HasSlimTrianglesWith.isHyperbolicWith`: a geodesic space with `δ`-slim triangles is
  `3 * δ`-hyperbolic.
* `Metric.IsHyperbolicWith.hasSlimTrianglesWith`: a `δ`-hyperbolic space has `3 * δ`-slim
  triangles.
* `Metric.isHyperbolic_iff_exists_hasSlimTrianglesWith`: a geodesic space is hyperbolic if and
  only if it has `δ`-slim triangles for some `δ`.

## Implementation notes

`Metric.HasSlimTrianglesWith` asks the condition for the first side of every triangle only; the
other sides are the first sides of the rotated triangles.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Definition 7.2.1 and
  Exercise 7.E.10
* [M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
  Definition III.H.1.1 and Proposition III.H.1.22

## Tags

slim triangles, Rips condition, hyperbolic space, Gromov hyperbolic, four-point condition
-/

@[expose] public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] {δ : ℝ}

/-- A pseudometric space has **`δ`-slim triangles** if for every geodesic triangle, every point of
one side is within distance `δ` of a point of one of the other two sides.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 7.2.1. -/
def HasSlimTrianglesWith (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  ∀ ⦃x y z : X⦄ ⦃a b c : Set X⦄,
    IsGeodesicSegment a x y → IsGeodesicSegment b y z → IsGeodesicSegment c z x →
    ∀ p ∈ a, ∃ q ∈ b ∪ c, dist p q ≤ δ

/-- A geodesic space with `δ`-slim triangles satisfies the four-point condition with constant
`3 * δ`. -/
theorem HasSlimTrianglesWith.isHyperbolicWith (hX : IsGeodesicSpace X)
    (h : HasSlimTrianglesWith X δ) : IsHyperbolicWith X (3 * δ) := by
  sorry

/-- A space satisfying the four-point condition with constant `δ` has `3 * δ`-slim triangles. -/
theorem IsHyperbolicWith.hasSlimTrianglesWith (h : IsHyperbolicWith X δ) :
    HasSlimTrianglesWith X (3 * δ) := by
  sorry

/-- A geodesic space is hyperbolic if and only if it has `δ`-slim triangles for some `δ`.

[C. Löh, *Geometric Group Theory*][loeh2017], Exercise 7.E.10;
[M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
Proposition III.H.1.22. -/
theorem isHyperbolic_iff_exists_hasSlimTrianglesWith (hX : IsGeodesicSpace X) :
    IsHyperbolic X ↔ ∃ δ, HasSlimTrianglesWith X δ := by
  sorry

end Metric
