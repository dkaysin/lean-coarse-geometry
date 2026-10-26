/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Topology.MetricSpace.Hyperbolic
public import Coarse.Topology.MetricSpace.QuasiGeodesic

/-!
# Stability of quasi-geodesics

In a geodesic space with `δ`-slim triangles, a `(c, b)`-quasi-geodesic stays within a bounded
distance of any geodesic segment with the same endpoints, and conversely: the Hausdorff distance
between its image and the segment is bounded by a constant that depends only on the space, `c` and
`b`. Hence having
slim triangles passes back along quasi-isometric embeddings of geodesic spaces.

## Main statements

* `Metric.HasSlimTrianglesWith.exists_hausdorffDist_le`: stability of quasi-geodesics.
* `Metric.IsQuasiIsometricEmbedding.exists_hasSlimTrianglesWith`: a geodesic space with a
  quasi-isometric embedding into a geodesic space with slim triangles has slim triangles.

## Implementation notes

The bound is uniform over the quasi-geodesics and geodesics of one space; the books' constant
depends only on `δ`, `c` and `b`.

## References

* [M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
  Theorems III.H.1.7 and III.H.1.9
* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Theorem 7.2.11 and
  Corollary 7.2.13

## Tags

stability of quasi-geodesics, Morse lemma, slim triangles, hyperbolic space
-/

@[expose] public section

open scoped NNReal

namespace Metric

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {δ : ℝ}

/-- **Stability of quasi-geodesics**: in a geodesic space with `δ`-slim triangles, for all `c` and
`b` there is `R` such that the image of every `(c, b)`-quasi-geodesic is within Hausdorff distance
`R` of every geodesic segment with the same endpoints.

[M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
Theorem III.H.1.7; [C. Löh, *Geometric Group Theory*][loeh2017], Theorem 7.2.11. -/
theorem HasSlimTrianglesWith.exists_hausdorffDist_le (hX : IsGeodesicSpace X)
    (h : HasSlimTrianglesWith X δ) (c b : ℝ≥0) :
    ∃ R, ∀ ⦃γ : ℝ → X⦄ ⦃t t' : ℝ⦄ ⦃s : Set X⦄ ⦃x y : X⦄, IsQuasiGeodesicWith c b γ t t' x y →
      IsGeodesicSegment s x y → hausdorffDist (γ '' Set.Icc t t') s ≤ R := by
  sorry

/-- A geodesic space with a quasi-isometric embedding into a geodesic space with `δ`-slim triangles
has `δ'`-slim triangles for some `δ'`.

[M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
Theorem III.H.1.9; [C. Löh, *Geometric Group Theory*][loeh2017], Corollary 7.2.13. -/
theorem IsQuasiIsometricEmbedding.exists_hasSlimTrianglesWith {f : X → Y}
    (hf : IsQuasiIsometricEmbedding f) (hX : IsGeodesicSpace X) (hY : IsGeodesicSpace Y)
    (h : HasSlimTrianglesWith Y δ) : ∃ δ', HasSlimTrianglesWith X δ' := by
  sorry

end Metric
