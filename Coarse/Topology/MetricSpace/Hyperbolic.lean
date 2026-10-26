/-
Copyright (c) 2026 Hang Lu Su, Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Katerina Hristova, Dmitry Kaysin
-/
module

public import Coarse.Topology.MetricSpace.Geodesic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.GromovProduct
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Isometry
/-!

# Gromov hyperbolic pseudometric spaces

## Main definitions

* `IsHyperbolicWith`: A pseudometric space is hyperbolic with constant `δ` if and only if for all
  `w x y z` the four-point condition
  `min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds.
* `IsHyperbolic`: A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some constant `δ`.
* `HasSlimTrianglesWith X δ`: every geodesic triangle in `X` is `δ`-slim: every point of each side
  is within distance `δ` of a point of one of the other two sides.

## Main results

* `IsHyperbolicWith.of_isometry`: A space with an isometry into a `δ`-hyperbolic space is also
  `δ`-hyperbolic.
* `IsHyperbolicWith.subtype`: A subspace of a δ-hyperbolic space is `δ`-hyperbolic.
* `isHyperbolicWith_diam_univ`: A bounded space is `δ`-hyperbolic with respect to its diameter.
* `HasSlimTrianglesWith.infDist_le_gromovProduct_add`: in a geodesic space with `δ`-slim triangles,
  the distance from `p` to a geodesic segment from `x` to `y` is at most
  `gromovProduct p x y + 2 * δ`.
* `HasSlimTrianglesWith.isHyperbolicWith`: a geodesic space with `δ`-slim triangles is
  `3 * δ`-hyperbolic.
* `IsHyperbolicWith.hasSlimTrianglesWith`: a `δ`-hyperbolic space has `3 * δ`-slim triangles.
* `isHyperbolic_iff_exists_hasSlimTrianglesWith`: a geodesic space is hyperbolic if and only if it
  has `δ`-slim triangles for some `δ`.

## Implementation notes

* `IsHyperbolicWith X δ` follows `LipschitzWith` and `HolderWith`. A space can admit many
  hyperbolicity constants. The typeclass `IsHyperbolic X` records only the existence of a constant,
  as `LipschitzMul` and `MemHolder` do. Using a typeclass lets instance search infer hyperbolicity
  for subtypes and bounded spaces.
* The constant `δ` in `IsHyperbolicWith X δ` is a real number. For a non-empty space,
  taking `w = x = y = z` in the four-point condition yields `0 ≤ δ`.
* `HasSlimTrianglesWith` asks the condition for the first side of every triangle only; the other
  sides are the first sides of the rotated triangles.

Copied from mathlib4 PR #43723 (`Mathlib/Topology/MetricSpace/Hyperbolic.lean`), except the
section on slim triangles, which is ours; see `ATTRIBUTION.md`.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Definition 7.2.1 and
  Exercise 7.E.10
* [M. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*][bridson1999],
  Definition III.H.1.1 and Proposition III.H.1.22
* [C. Druțu, M. Kapovich, *Geometric Group Theory*][drutu2018], Lemma 11.22

## Tags

Gromov hyperbolic pseudometric space, slim triangles, Rips condition, four-point condition
-/

@[expose] public section

attribute [grind =] Bornology.isBounded_univ

namespace Metric

/-! ### δ-hyperbolic spaces -/

/-- A pseudometric space is `δ`-hyperbolic if for all `w x y z` the four-point condition
`min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds. -/
@[wikidata Q3828581]
def IsHyperbolicWith (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  ∀ w x y z : X, min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z

variable {X Y : Type*} {δ δ' : ℝ} [PseudoMetricSpace X] [PseudoMetricSpace Y]

namespace IsHyperbolicWith

/-- If a space is δ-hyperbolic, and δ ≤ δ', then it is also δ'-hyperbolic. -/
@[grind →]
lemma mono (h : IsHyperbolicWith X δ) (hδ : δ ≤ δ') : IsHyperbolicWith X δ' := by
  grind [IsHyperbolicWith]

/-- A non-empty space being δ-hyperbolic implies that 0 ≤ δ. -/
@[grind →]
lemma nonneg [hX : Nonempty X] (h : IsHyperbolicWith X δ) : 0 ≤ δ := by
  obtain ⟨x⟩ := hX
  grind [h x x x x]

/-- A space with an isometry into a `δ`-hyperbolic space is also `δ`-hyperbolic. -/
@[grind →]
theorem of_isometry {f : X → Y} (h : IsHyperbolicWith Y δ) (hf : Isometry f) :
    IsHyperbolicWith X δ := by
  intro w x y z
  grind [h (f w) (f x) (f y) (f z), gromovProduct_eq, Isometry.dist_eq]

/-- A subspace of a δ-hyperbolic space is δ-hyperbolic. -/
@[grind .]
theorem subtype (h : IsHyperbolicWith X δ) (p : X → Prop) : IsHyperbolicWith (Subtype p) δ :=
  h.of_isometry isometry_subtype_coe

end IsHyperbolicWith

/-- A pseudometric space with all distances bounded above by `k` is `k`-hyperbolic. -/
lemma isHyperbolicWith_of_forall_dist_le {k : ℝ} (hk : ∀ x y : X, dist x y ≤ k) :
    IsHyperbolicWith X k := by
  grind [IsHyperbolicWith, gromovProduct_le_dist_left]

/-- A pseudometric space with at most one point is `0`-hyperbolic. -/
lemma isHyperbolicWith_zero_of_subsingleton [h : Subsingleton X] : IsHyperbolicWith X 0 :=
  isHyperbolicWith_of_forall_dist_le (by simp)

/-- A bounded space is δ-hyperbolic with respect to its diameter. -/
theorem isHyperbolicWith_diam_univ [BoundedSpace X] :
    IsHyperbolicWith X (diam (Set.univ : Set X)) :=
  isHyperbolicWith_of_forall_dist_le (by grind [dist_le_diam_of_mem])

/-! ### Hyperbolic spaces -/

/-- A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some real constant `δ`. -/
@[wikidata Q3828581]
class IsHyperbolic (X : Type*) [PseudoMetricSpace X] : Prop where
  exists_isHyperbolicWith : ∃ δ, IsHyperbolicWith X δ

/-- A subspace of a hyperbolic space is hyperbolic. -/
instance [h : IsHyperbolic X] (p : X → Prop) : IsHyperbolic (Subtype p) := by
  obtain ⟨_, hX⟩ := h
  exact ⟨_, hX.subtype p⟩

/-- Every bounded pseudometric space is hyperbolic. -/
instance [BoundedSpace X] : IsHyperbolic X := ⟨_, isHyperbolicWith_diam_univ⟩

/-! ### Slim triangles -/

/-- A pseudometric space has **`δ`-slim triangles** if for every geodesic triangle, every point of
one side is within distance `δ` of a point of one of the other two sides.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 7.2.1. -/
def HasSlimTrianglesWith (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  ∀ ⦃x y z : X⦄ ⦃a b c : Set X⦄,
    IsGeodesicSegment a x y → IsGeodesicSegment b y z → IsGeodesicSegment c z x →
    ∀ p ∈ a, ∃ q ∈ b ∪ c, dist p q ≤ δ

/-- In a geodesic space with `δ`-slim triangles, every point `p` is within
`gromovProduct p x y + 2 * δ` of a geodesic segment from `x` to `y`.

[C. Druțu, M. Kapovich, *Geometric Group Theory*][drutu2018], Lemma 11.22. -/
theorem HasSlimTrianglesWith.infDist_le_gromovProduct_add (hX : IsGeodesicSpace X)
    (h : HasSlimTrianglesWith X δ) {s : Set X} {x y : X} (hs : IsGeodesicSegment s x y) (p : X) :
    infDist p s ≤ gromovProduct p x y + 2 * δ := by
  sorry

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
