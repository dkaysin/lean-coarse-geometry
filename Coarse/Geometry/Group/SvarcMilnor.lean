/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Geometry.Group.WordMetricBounds
public import Coarse.Topology.Bornology.MetricallyProperSMul
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.GroupTheory.Finiteness

/-!
# The Švarc–Milnor lemma

A group acting isometrically, metrically properly and coboundedly on a nonempty coarsely
connected pseudometric space is finitely generated; if the space is moreover coarsely geodesic,
every orbit map is a quasi-isometry for the word metric of any finite generating family.

## Main statements

* `Group.fg_of_isCoboundedSMul`: the Švarc–Milnor lemma, finite generation.
* `Group.Generators.isQuasiIsometry_smul_const`: the Švarc–Milnor lemma, quasi-isometry.
* `Subgroup.isQuasiIsometry_subtype`: a subgroup of finite index of a finitely generated group is
  quasi-isometric to the group, by the inclusion.
* `Int.quasiIsometric_pi_euclideanSpace`: `ℤⁿ` with a word metric is quasi-isometric to `ℝⁿ`.

## Implementation notes

The space is assumed coarsely connected or coarsely geodesic (`Metric.IsCoarselyConnected`,
`Metric.IsCoarselyGeodesic`) in place of Löh's quasi-geodesic hypothesis. The count of steps
cannot be dropped from the quasi-isometry statement: `ℤ` acting by translations on `ℝ` with the
metric `√|x - y|` satisfies every other hypothesis, and its orbit maps are not quasi-isometries.

`ℤⁿ` is `Fin n → ℤ` with the word metric of an additive generating family
(`AddGroup.Generators.normedAddGroup`), passed explicitly because `Fin n → ℤ` already carries the
sup metric.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Proposition 5.4.1,
  Corollary 5.4.7 and Example 5.2.8

## Tags

Švarc–Milnor lemma, Milnor–Švarc lemma, quasi-isometry, word metric, geometric group theory
-/

@[expose] public section

variable {G X : Type*} [Group G] [PseudoMetricSpace X] [Nonempty X] [MulAction G X]
  [IsIsometricSMul G X]

/-- **Švarc–Milnor lemma**, finite generation: a group acting isometrically, metrically properly
and coboundedly on a nonempty coarsely connected pseudometric space is finitely generated. -/
theorem Group.fg_of_isCoboundedSMul
    (hX : Metric.IsCoarselyConnected X) (hprop : IsMetricallyProperSMul G X)
    (hcob : IsCoboundedSMul G X) : Group.FG G :=
  sorry

/-- **Švarc–Milnor lemma**, quasi-isometry: a group acting isometrically, metrically properly and
coboundedly on a nonempty coarsely geodesic pseudometric space is quasi-isometric to the space:
every orbit map `g ↦ g • x₀` is a quasi-isometry for the word metric of any finite generating
family. -/
theorem Group.Generators.isQuasiIsometry_smul_const {ι : Type*} [Finite ι] (P : Generators G ι)
    (hX : Metric.IsCoarselyGeodesic X)
    (hprop : IsMetricallyProperSMul G X) (hcob : IsCoboundedSMul G X) (x₀ : X) :
    letI := P.normedGroup
    Metric.IsQuasiIsometry fun g : G ↦ g • x₀ :=
  sorry

/-- A subgroup of finite index of a group with a finite generating family is quasi-isometric to
the group: the inclusion is a quasi-isometry for the word metrics of any finite generating
families. -/
theorem Subgroup.isQuasiIsometry_subtype (H : Subgroup G) [H.FiniteIndex] {ι κ : Type*}
    [Finite ι] [Finite κ] (P : Group.Generators G ι) (Q : Group.Generators H κ) :
    @Metric.IsQuasiIsometry H G Q.normedGroup.toPseudoMetricSpace
      P.normedGroup.toPseudoMetricSpace ((↑) : H → G) :=
  sorry

/-- `ℤⁿ` with the word metric of a finite generating family is quasi-isometric to `ℝⁿ`.

[C. Löh, *Geometric Group Theory*][loeh2017], Example 5.2.8. -/
theorem Int.quasiIsometric_pi_euclideanSpace {n : ℕ} {ι : Type*} [Finite ι]
    (P : AddGroup.Generators (Fin n → ℤ) ι) :
    @Metric.QuasiIsometric (Fin n → ℤ) (EuclideanSpace ℝ (Fin n))
      P.normedAddGroup.toPseudoMetricSpace _ :=
  sorry
