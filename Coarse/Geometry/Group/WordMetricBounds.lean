/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Geometry.Group.CayleySimpleGraph
public import Coarse.Geometry.Group.WithWordMetric
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
* `Group.Generators.WithWordMetric.exists_lipschitzWith_congr`: for a finite generating family
  `P`, the identity of the group is Lipschitz from the word metric of `P` to any other word metric.
* `Group.Generators.WithWordMetric.isQuasiIsometry_congr`: for two finite generating families,
  the identity of the group is a quasi-isometry between the two word metrics.

## Implementation notes

The word metric of `P` is the metric of `P.WithWordMetric`. The bounds are stated with
`wordLength`, for maps out of `G`.

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
  -- Apply `dist_le_mul_wordLength` to `G → Q.WithWordMetric`, which moves `g` and `g * P.val i`
  -- apart by `|P.val i|_Q`.
  have hg := P.dist_le_mul_wordLength (φ := WithWordMetric.toWordMetric Q) (K := K)
    (fun g i ↦ by simpa [WithWordMetric.dist_eq] using hK i) 1 g
  simp only [WithWordMetric.dist_eq, inv_one, one_mul, NNReal.coe_natCast] at hg
  exact_mod_cast hg

/-- For a finite generating family, there are finitely many elements of word length at most
`n`. -/
theorem finite_setOf_wordLength_le [Finite ι] (n : ℕ) : {g | P.wordLength g ≤ n}.Finite :=
  ((List.finite_length_le (ι × Bool) n).image P.wordProd).subset fun g hg ↦ by
    obtain ⟨l, hl, rfl⟩ := (P.wordLength_le_iff g).1 hg
    exact ⟨l, hl, rfl⟩

/-- A group with the word metric of a generating family is `(1, 1, 0)`-coarsely geodesic. -/
theorem isCoarselyGeodesicWith : Metric.IsCoarselyGeodesicWith P.WithWordMetric 1 1 0 := by
  -- Adjacent vertices of the Cayley graph differ by a letter, so they are at distance at most
  -- `1`: walks in the Cayley graph are `1`-chains.
  let φ : P.cayleySimpleGraph →g Metric.ripsGraph P.WithWordMetric 1 :=
    ⟨WithWordMetric.toWordMetric P, fun {g h} hgh ↦ by
      obtain ⟨hne, x, hx⟩ := (P.cayleySimpleGraph_adj g h).1 hgh
      refine ⟨fun h' ↦ hne (congrArg WithWordMetric.ofWordMetric h'), ?_⟩
      rw [WithWordMetric.dist_eq, WithWordMetric.ofWordMetric_toWordMetric,
        WithWordMetric.ofWordMetric_toWordMetric, ← hx]
      exact_mod_cast P.wordLength_wordProd_le [x]⟩
  -- A geodesic word for `x⁻¹ * y` gives a walk in the Cayley graph from `x` to `y`.
  intro x y
  obtain ⟨l, hl, hlg⟩ := P.exists_isGeodesic (x.ofWordMetric⁻¹ * y.ofWordMetric)
  obtain ⟨p, hp⟩ := P.exists_walk_of_word x.ofWordMetric l
  refine ⟨(p.map φ).copy rfl (by simp [φ, hlg]), ?_⟩
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map, WithWordMetric.dist_eq, ← hlg,
    hl.eq]
  simpa using hp

namespace WithWordMetric

variable (Q : Generators G κ)

/-- For a finite generating family `P`, the identity of `G` is Lipschitz from the word metric of
`P` to the word metric of any generating family `Q`. -/
theorem exists_lipschitzWith_congr [Finite ι] : ∃ K, LipschitzWith K (congr P Q) := by
  -- Bound the `Q`-lengths of the generators of `P`.
  obtain ⟨K, hK⟩ := (Set.finite_range fun i ↦ Q.wordLength (P.val i)).bddAbove
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [dist_eq, dist_eq, ofWordMetric_congr, ofWordMetric_congr, NNReal.coe_natCast]
  exact_mod_cast P.wordLength_le_mul_wordLength Q (fun i ↦ hK ⟨i, rfl⟩) _

/-- For finite generating families `P` and `Q` of `G`, the identity of `G` is a quasi-isometry
from the word metric of `P` to the word metric of `Q`.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.2.5. -/
theorem isQuasiIsometry_congr [Finite ι] [Finite κ] : Metric.IsQuasiIsometry (congr P Q) := by
  -- `congr P Q` is a bijection, Lipschitz in both directions.
  obtain ⟨K, hPQ⟩ := exists_lipschitzWith_congr P Q
  obtain ⟨K', hQP⟩ := exists_lipschitzWith_congr Q P
  exact Metric.isQuasiIsometry_of_bilipschitz (hQP.to_rightInverse fun _ ↦ rfl) hPQ
    (congr P Q).surjective

end WithWordMetric

end Group.Generators
