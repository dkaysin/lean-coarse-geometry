/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Geometry.Group.WordMetric
public import Coarse.Topology.MetricSpace.CoarselyGeodesic
public import Coarse.Topology.MetricSpace.QuasiIsometry

/-!
# Bounds for the word metric

Bounds relating the word length of a generating family to distances and to other generating
families, and the consequences for the word metric up to quasi-isometry.

## Main statements

* `Group.Generators.dist_le_mul_wordLength`: a map out of `G` that moves points by at most `K`
  under right multiplication by a generator satisfies `dist (φ g) (φ h) ≤ K * |g⁻¹ * h|`
  (the Lipschitz principle).
* `Group.Generators.wordLength_le_mul_wordLength`: the word length for `Q` is at most `M` times
  the word length for `P` if every generator of `P` has `Q`-length at most `M`.
* `Group.Generators.finite_setOf_wordLength_le`: balls of the word metric of a finite generating
  family are finite.
* `Group.Generators.isCoarselyGeodesicWith`: a group with the word metric is
  `(1, 1, 0)`-coarsely geodesic.
* `Group.Generators.isQuasiIsometry_id`: for two finite generating families, the identity is a
  quasi-isometry between the two word metrics.

## Implementation notes

As in `Coarse.Geometry.Group.WordMetric`, the word metric is installed with
`letI := P.normedGroup`. Statements with two word metrics on the same group pass the two
instances explicitly.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Proposition 5.2.5

## Tags

word metric, word length, generating family, quasi-isometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

namespace Group.Generators

variable {G ι κ : Type*} [Group G] (P : Generators G ι)

/-- **Lipschitz principle.** If right multiplication by a generator moves the values of
`φ : G → X` by at most `K`, then `dist (φ g) (φ h) ≤ K * |g⁻¹ * h|` for the word length of `P`. -/
theorem dist_le_mul_wordLength {X : Type*} [PseudoMetricSpace X] {φ : G → X} {K : ℝ}
    (hφ : ∀ g i, dist (φ g) (φ (g * P.val i)) ≤ K) (g h : G) :
    dist (φ g) (φ h) ≤ K * P.wordLength (g⁻¹ * h) :=
  sorry

/-- If every generator of `P` has word length at most `M` for `Q`, then the word length for `Q` is
at most `M` times the word length for `P`.

[C. Löh, *Geometric Group Theory*][loeh2017], proof of Proposition 5.2.5. -/
theorem wordLength_le_mul_wordLength (Q : Generators G κ) {M : ℕ}
    (hM : ∀ i, Q.wordLength (P.val i) ≤ M) (g : G) :
    Q.wordLength g ≤ M * P.wordLength g :=
  sorry

/-- For a finite generating family, there are finitely many elements of word length at most
`n`. -/
theorem finite_setOf_wordLength_le [Finite ι] (n : ℕ) : {g | P.wordLength g ≤ n}.Finite :=
  sorry

/-- A group with the word metric of a generating family is `(1, 1, 0)`-coarsely geodesic. -/
theorem isCoarselyGeodesicWith :
    letI := P.normedGroup
    Metric.IsCoarselyGeodesicWith G 1 1 0 :=
  sorry

/-- **Change of generators.** For finite generating families `P` and `Q` of `G`, the identity of
`G` is a quasi-isometry from the word metric of `P` to the word metric of `Q`.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.2.5. -/
theorem isQuasiIsometry_id [Finite ι] [Finite κ] (Q : Generators G κ) :
    @Metric.IsQuasiIsometry G G P.normedGroup.toPseudoMetricSpace
      Q.normedGroup.toPseudoMetricSpace id :=
  sorry

end Group.Generators
