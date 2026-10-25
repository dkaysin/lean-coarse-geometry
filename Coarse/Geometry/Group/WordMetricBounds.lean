/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Geometry.Group.CayleySimpleGraph
public import Coarse.Geometry.Group.WordMetric
public import Coarse.Topology.MetricSpace.CoarselyGeodesic
public import Coarse.Topology.MetricSpace.QuasiIsometry

import Mathlib.Data.Set.Finite.List

/-!
# Bounds for the word metric

Bounds relating the word length of a generating family to distances and to other generating
families, and the consequences for the word metric up to quasi-isometry.

## Main statements

* `Group.Generators.dist_le_mul_wordLength`: a map out of `G` that moves points by at most `K`
  under right multiplication by a generator satisfies `dist (φ g) (φ h) ≤ K * |g⁻¹ * h|`.
* `Group.Generators.wordLength_le_mul_wordLength`: the word length for `Q` is at most `K` times
  the word length for `P` if every generator of `P` has `Q`-length at most `K`.
* `Group.Generators.finite_setOf_wordLength_le`: balls of the word metric of a finite generating
  family are finite.
* `Group.Generators.isCoarselyGeodesicWith`: a group with the word metric is
  `(1, 1, 0)`-coarsely geodesic.
* `Group.Generators.isQuasiIsometry_id`: for two finite generating families, the identity is a
  quasi-isometry between the two word metrics.

## Implementation notes

As in `Coarse.Geometry.Group.WordMetric`, the word metric is installed with
`letI := P.normedGroup`. Statements with two word metrics on the same group pass the two
instances explicitly. The bounds are stated with `wordLength`, which puts no metric on the group,
so that applying them to a second word metric on the same group needs only one instance.

## References

* [M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
  Lemma I.8.18
* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Proposition 5.2.5

## Tags

word metric, word length, generating family, quasi-isometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

namespace Group.Generators

variable {G ι κ : Type*} [Group G] (P : Generators G ι)

/-- If right multiplication by a generator moves the values of `φ : G → X` by at most `K`, then
`dist (φ g) (φ h) ≤ K * |g⁻¹ * h|` for the word length of `P`: `φ` is `K`-Lipschitz for the word
metric of `P`.

[M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
Lemma I.8.18, for orbit maps of isometric actions. -/
theorem dist_le_mul_wordLength {X : Type*} [PseudoMetricSpace X] {φ : G → X} {K : ℝ≥0}
    (hφ : ∀ g i, dist (φ g) (φ (g * P.val i)) ≤ K) (g h : G) :
    dist (φ g) (φ h) ≤ K * P.wordLength (g⁻¹ * h) := by
  -- Adjacent vertices of the Cayley graph differ by right multiplication by a generator, in one
  -- direction or the other, so `φ` moves them by at most `K`.
  have hadj (g h : G) (hgh : P.cayleySimpleGraph.Adj g h) : dist (φ g) (φ h) ≤ K := by
    obtain ⟨-, _, ⟨i, rfl⟩, rfl | rfl⟩ := (SimpleGraph.mulCayley_adj' _ g h).1 hgh
    · exact hφ g i
    · rw [dist_comm]
      exact hφ h i
  -- A geodesic word for `g⁻¹ * h` gives a walk in the Cayley graph from `g` to `h`.
  obtain ⟨l, hl, hlg⟩ := P.exists_isGeodesic (g⁻¹ * h)
  obtain ⟨p, hp⟩ := P.exists_walk_of_word g l
  calc dist (φ g) (φ h) = dist (φ g) (φ (g * P.wordProd l)) := by rw [hlg, mul_inv_cancel_left]
    _ ≤ K * p.length := p.dist_le_mul_length hadj
    _ ≤ K * l.length := by gcongr
    _ = K * P.wordLength (g⁻¹ * h) := by rw [← hlg, hl.eq]

/-- If every generator of `P` has word length at most `K` for `Q`, then the word length for `Q` is
at most `K` times the word length for `P`.

[C. Löh, *Geometric Group Theory*][loeh2017], proof of Proposition 5.2.5. -/
theorem wordLength_le_mul_wordLength (Q : Generators G κ) {K : ℕ}
    (hK : ∀ i, Q.wordLength (P.val i) ≤ K) (g : G) :
    Q.wordLength g ≤ K * P.wordLength g := by
  -- Apply `dist_le_mul_wordLength` to the identity into the word metric of `Q`, in which
  -- `dist g (g * P.val i) = |P.val i|_Q`.
  let := Q.normedGroup
  have hg := P.dist_le_mul_wordLength (φ := id) (K := K) (fun g i ↦ by
    change (Q.wordLength (g⁻¹ * (g * P.val i)) : ℝ) ≤ ((K : ℝ≥0) : ℝ)
    simpa using hK i) 1 g
  change (Q.wordLength (1⁻¹ * g) : ℝ) ≤ ((K : ℝ≥0) : ℝ) * P.wordLength (1⁻¹ * g) at hg
  simp only [inv_one, one_mul, NNReal.coe_natCast] at hg
  exact_mod_cast hg

/-- For a finite generating family, there are finitely many elements of word length at most
`n`. -/
theorem finite_setOf_wordLength_le [Finite ι] (n : ℕ) : {g | P.wordLength g ≤ n}.Finite :=
  ((List.finite_length_le (ι × Bool) n).image P.wordProd).subset fun g hg ↦ by
    obtain ⟨l, hl, rfl⟩ := (P.wordLength_le_iff g).1 hg
    exact ⟨l, hl, rfl⟩

/-- A group with the word metric of a generating family is `(1, 1, 0)`-coarsely geodesic. -/
theorem isCoarselyGeodesicWith :
    letI := P.normedGroup
    Metric.IsCoarselyGeodesicWith G 1 1 0 :=
  sorry

/-- For finite generating families `P` and `Q` of `G`, the identity of
`G` is a quasi-isometry from the word metric of `P` to the word metric of `Q`.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.2.5. -/
theorem isQuasiIsometry_id [Finite ι] [Finite κ] (Q : Generators G κ) :
    @Metric.IsQuasiIsometry G G P.normedGroup.toPseudoMetricSpace
      Q.normedGroup.toPseudoMetricSpace id :=
  sorry

end Group.Generators
