/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Topology.MetricSpace.CoarseAntilipschitz
public import Coarse.Topology.MetricSpace.CoarseLipschitz
public import Coarse.Topology.MetricSpace.FiniteDistance
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Quasi-isometric embeddings and quasi-isometries

A map `f` between pseudometric spaces is a *`(c, b)`-quasi-isometric embedding* if
`c⁻¹ * dist x y - b ≤ dist (f x) (f y) ≤ c * dist x y + b` for all `x` and `y`.
Quasi-isometric embeddings need not be injective or continuous.

A *quasi-isometry* between pseudometric spaces is a quasi-isometric embedding that is invertible
up to finite distance: it has a quasi-inverse, a quasi-isometric embedding in the other direction
such that both composites have finite distance from the identity. Two spaces are *quasi-isometric*
if there is a quasi-isometry between them. Quasi-isometries need not be injective, surjective or
continuous.

A map has *quasi-dense range* if every point of the codomain is within a uniformly bounded
distance of its range. A map is a quasi-isometry if and only if it is a quasi-isometric embedding
with quasi-dense range.

## Main definitions

* `Metric.IsQuasiIsometricEmbeddingWith c b f`: `f` is a `(c, b)`-quasi-isometric embedding.
* `Metric.IsQuasiIsometricEmbedding f`: `f` is a `(c, b)`-quasi-isometric embedding for some
  constants `c` and `b`.
* `Metric.IsQuasiIsometry f`: `f` is a quasi-isometry.
* `Metric.QuasiIsometric α β`: the pseudometric spaces `α` and `β` are quasi-isometric.
* `Metric.QuasiDenseRange f`: there is a constant `c` such that every point of the codomain is
  within distance `c` of a point of the range of `f`.

## Main statements

* `Metric.IsQuasiIsometry.comp`: the composition of two quasi-isometries is a quasi-isometry.
* `Metric.isQuasiIsometry_iff_quasiDenseRange`: a map is a quasi-isometry if and only if it is a
  quasi-isometric embedding with quasi-dense range.
* `Metric.isQuasiIsometry_of_bilipschitz`: a surjective bilipschitz map is a quasi-isometry.
* `Metric.CoarseLipschitzWith.isQuasiIsometry`: a coarse Lipschitz map with a coarse Lipschitz
  quasi-inverse is a quasi-isometry.

## Implementation notes

The lower bound of a `(c, b)`-quasi-isometric embedding is stated without division or
subtraction, as `Metric.CoarseAntilipschitzWith c (c * b) f`. For `c ≠ 0` this is equivalent to
`c⁻¹ * dist x y - b ≤ dist (f x) (f y)`, see `Metric.coarseAntilipschitzWith_iff_inv_mul_sub_le`.

The constants `c` and `b` have type `ℝ≥0` and are not required to be positive.

A quasi-isometry is defined by the existence of a quasi-inverse, and not as a quasi-isometric
embedding with quasi-dense range; `Metric.isQuasiIsometry_iff_quasiDenseRange` relates the two.

`Metric.QuasiDenseRange f` is stated with `dist`. It says that `Set.range f` is a `C`-cover of the
whole space for some `C`, in the sense of `Metric.IsCover`, which is stated with `edist`; see
`Metric.quasiDenseRange_iff_exists_isCover`.

## References

* [C. Löh, *Geometric Group Theory: An Introduction*][loeh2017], Definition 5.1.6 and
  Proposition 5.1.10
* [C. Druțu, M. Kapovich, *Geometric Group Theory*][drutu2018], Definition 8.10

## Tags

quasi-isometric embedding, quasi-isometry, quasi-isometric, quasi-inverse, quasi-dense,
coarsely dense, coarsely surjective, coarse geometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

namespace Metric

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
  {c b c' b' L₁ C₁ L₂ C₂ : ℝ≥0} {f : α → β}

/-! ### Quasi-isometric embeddings -/

/-- A map `f` between pseudometric spaces is a **`(c, b)`-quasi-isometric embedding** if
`c⁻¹ * dist x y - b ≤ dist (f x) (f y) ≤ c * dist x y + b` for all `x` and `y`. The lower bound is
stated as `Metric.CoarseAntilipschitzWith c (c * b) f`; see
`Metric.coarseAntilipschitzWith_iff_inv_mul_sub_le` for the equivalence of the two forms.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.1.6. -/
structure IsQuasiIsometricEmbeddingWith (c b : ℝ≥0) (f : α → β) : Prop where
  coarseLipschitzWith : CoarseLipschitzWith c b f
  /-- The lower bound: `dist x y ≤ c * dist (f x) (f y) + c * b`. -/
  coarseAntilipschitzWith : CoarseAntilipschitzWith c (c * b) f

/-- A `(c, b)`-quasi-isometric embedding is a `(c', b')`-quasi-isometric embedding for `c ≤ c'`
and `b ≤ b'`. -/
theorem IsQuasiIsometricEmbeddingWith.mono (hf : IsQuasiIsometricEmbeddingWith c b f)
    (hc : c ≤ c') (hb : b ≤ b') : IsQuasiIsometricEmbeddingWith c' b' f :=
  ⟨hf.coarseLipschitzWith.mono hc hb, hf.coarseAntilipschitzWith.mono hc (by gcongr)⟩

/-- A map `f` between pseudometric spaces is a **quasi-isometric embedding** if it is a
`(c, b)`-quasi-isometric embedding for some constants `c` and `b`.
[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.1.6. -/
def IsQuasiIsometricEmbedding (f : α → β) : Prop :=
  ∃ c b, IsQuasiIsometricEmbeddingWith c b f

/-- A coarse antilipschitz map that is also coarse Lipschitz, for possibly different constants,
is a quasi-isometric embedding. -/
theorem CoarseAntilipschitzWith.isQuasiIsometricEmbedding
    (hf : CoarseAntilipschitzWith L₂ C₂ f) (hf' : CoarseLipschitzWith L₁ C₁ f) :
    IsQuasiIsometricEmbedding f := by
  refine ⟨max (max L₁ L₂) 1, max C₁ C₂, ?_⟩
  have hC₂ : C₂ ≤ max (max L₁ L₂) 1 * max C₁ C₂ := by
    have hM : (1 : ℝ≥0) ≤ max (max L₁ L₂) 1 := by simp
    calc C₂ ≤ max C₁ C₂ := by simp
      _ = 1 * max C₁ C₂ := by simp
      _ ≤ max (max L₁ L₂) 1 * max C₁ C₂ := by gcongr
  constructor
  · exact hf'.mono (by simp) (by simp)
  · exact hf.mono (by simp) (hC₂)

/-- The composition of two quasi-isometric embeddings is a quasi-isometric embedding.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.1.11 (4). -/
theorem IsQuasiIsometricEmbedding.comp {γ : Type*} [PseudoMetricSpace γ] {g : β → γ}
    (hg : IsQuasiIsometricEmbedding g) (hf : IsQuasiIsometricEmbedding f) :
    IsQuasiIsometricEmbedding (g ∘ f) :=
  let ⟨_, _, hg⟩ := hg
  let ⟨_, _, hf⟩ := hf
  (hg.coarseAntilipschitzWith.comp hf.coarseAntilipschitzWith).isQuasiIsometricEmbedding
    (hg.coarseLipschitzWith.comp hf.coarseLipschitzWith)

/-- Postcomposition with an `(L, C)`-coarse Lipschitz map preserves finite distance: distance `D`
becomes `L * D + C`.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.1.11 (3). -/
theorem HasFiniteDist.comp_left {ι γ : Type*} [PseudoMetricSpace γ] {g : β → γ} {k k' : ι → β}
    (h : HasFiniteDist k k') (hg : CoarseLipschitzWith L₁ C₁ g) :
    HasFiniteDist (g ∘ k) (g ∘ k') :=
  let ⟨D, hD⟩ := h
  ⟨L₁ * D + C₁, fun x ↦ by grw [Function.comp_apply, Function.comp_apply, hg (k x), hD]; simp⟩

/-! ### Quasi-isometries -/

/-- A map `f` between pseudometric spaces is a **quasi-isometry** if it is a quasi-isometric
embedding and has a quasi-inverse: a quasi-isometric embedding `g` in the other direction such
that `g ∘ f` and `f ∘ g` have finite distance from the identity.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.1.6. -/
structure IsQuasiIsometry (f : α → β) : Prop where
  isQuasiIsometricEmbedding : IsQuasiIsometricEmbedding f
  exists_quasiInverse :
    ∃ g : β → α, IsQuasiIsometricEmbedding g ∧ HasFiniteDist (g ∘ f) id ∧ HasFiniteDist (f ∘ g) id

/-- Two pseudometric spaces are **quasi-isometric** if there is a quasi-isometry.

[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.1.6. -/
def QuasiIsometric (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β] : Prop :=
  ∃ f : α → β, IsQuasiIsometry f

/-- The composition of two quasi-isometries is a quasi-isometry.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.1.11 (5). -/
theorem IsQuasiIsometry.comp {γ : Type*} [PseudoMetricSpace γ] {g : β → γ}
    (hg : IsQuasiIsometry g) (hf : IsQuasiIsometry f) : IsQuasiIsometry (g ∘ f) := by
  obtain ⟨hg, g', hg', hgg, hgg'⟩ := hg
  obtain ⟨hf, f', hf', hff, hff'⟩ := hf
  refine ⟨hg.comp hf, f' ∘ g', hf'.comp hg', ?_, ?_⟩
  · -- `f' ∘ g' ∘ g ∘ f` is near `f' ∘ f`, which is near the identity.
    obtain ⟨_, _, hf'⟩ := hf'
    exact ((hgg.comp_right f).comp_left hf'.coarseLipschitzWith).trans hff
  · -- `g ∘ f ∘ f' ∘ g'` is near `g ∘ g'`, which is near the identity.
    obtain ⟨_, _, hg⟩ := hg
    exact ((hff'.comp_right g').comp_left hg.coarseLipschitzWith).trans hgg'

namespace QuasiIsometric

/-- Every pseudometric space is quasi-isometric to itself. -/
@[refl]
theorem refl (α : Type*) [PseudoMetricSpace α] : QuasiIsometric α α :=
  have h : IsQuasiIsometricEmbedding (id : α → α) :=
    ⟨1, 0, LipschitzWith.id.coarseLipschitzWith, by
      simpa using AntilipschitzWith.id.coarseAntilipschitzWith⟩
  ⟨id, h, id, h, .rfl, .rfl⟩

/-- Being quasi-isometric is symmetric. -/
@[symm]
theorem symm (h : QuasiIsometric α β) : QuasiIsometric β α :=
  let ⟨f, hf, g, hg, hgf, hfg⟩ := h
  ⟨g, hg, f, hf, hfg, hgf⟩

/-- Being quasi-isometric is transitive. -/
@[trans]
theorem trans {γ : Type*} [PseudoMetricSpace γ] (h₁ : QuasiIsometric α β)
    (h₂ : QuasiIsometric β γ) : QuasiIsometric α γ :=
  let ⟨_, hf⟩ := h₁
  let ⟨_, hg⟩ := h₂
  ⟨_, hg.comp hf⟩

end QuasiIsometric

/-! ### Quasi-dense range -/

/-- A map `f` into a pseudometric space has **quasi-dense range** if there is a constant `c` such
that every point of the codomain is within distance `c` of a point of the range of `f`.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.1.10. -/
def QuasiDenseRange {ι : Type*} (f : ι → β) : Prop :=
  ∃ c : ℝ≥0, ∀ y, ∃ x, dist (f x) y ≤ c

/-- A map has quasi-dense range if and only if its range is a `c`-cover of the whole codomain for
some constant `c`. -/
lemma quasiDenseRange_iff_exists_isCover {ι : Type*} {f : ι → β} :
    QuasiDenseRange f ↔ ∃ c : ℝ≥0, IsCover c Set.univ (Set.range f) := by
  refine exists_congr fun c ↦ ⟨fun h y _ ↦ ?_, fun h y ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h y
    exact ⟨f x, Set.mem_range_self x, by simpa [edist_dist, dist_comm] using hx⟩
  · obtain ⟨_, ⟨x, rfl⟩, hx⟩ := h (Set.mem_univ y)
    exact ⟨x, by simpa [edist_dist, dist_comm] using hx⟩

namespace IsQuasiIsometricEmbedding

variable {g : β → α}

/-- If `f` is a quasi-isometric embedding and `f ∘ g` has finite distance from the identity,
then `g` is a quasi-isometric embedding.

[C. Löh, *Geometric Group Theory*][loeh2017], proof of Proposition 5.1.10. -/
lemma of_hasFiniteDist_comp_id (hf : IsQuasiIsometricEmbedding f)
    (hfg : HasFiniteDist (f ∘ g) id) : IsQuasiIsometricEmbedding g := by
  obtain ⟨c, b, hf⟩ := hf
  obtain ⟨D, hD⟩ := hfg
  simp only [Function.comp_apply, id_eq] at hD
  -- `dist (f (g y)) (f (g y'))` and `dist y y'` differ by at most `2 * D`.
  have h₁ : CoarseLipschitzWith c (c * (2 * D + b)) g := fun y y' ↦ by
    have h := dist_triangle4 (f (g y)) y y' (f (g y'))
    grw [hf.coarseAntilipschitzWith (g y) (g y'), h, hD y, dist_comm y', hD y']
    push_cast
    exact le_of_eq (by ring)
  have h₂ : CoarseAntilipschitzWith c (2 * D + b) g := fun y y' ↦ by
    have h := dist_triangle4 y (f (g y)) (f (g y')) y'
    grw [h, dist_comm y, hD y, hD y', hf.coarseLipschitzWith (g y) (g y')]
    push_cast
    exact le_of_eq (by ring)
  exact h₂.isQuasiIsometricEmbedding h₁

/-- If `f` is a quasi-isometric embedding and `f ∘ g` has finite distance from the identity, then
so does `g ∘ f`.

[C. Löh, *Geometric Group Theory*][loeh2017], proof of Proposition 5.1.10. -/
lemma hasFiniteDist_comp_id (hf : IsQuasiIsometricEmbedding f)
    (hfg : HasFiniteDist (f ∘ g) id) : HasFiniteDist (g ∘ f) id := by
  obtain ⟨c, b, hf⟩ := hf
  obtain ⟨D, hD⟩ := hfg
  simp only [Function.comp_apply, id_eq] at hD
  -- `f (g (f x))` is within `D` of `f x`, so the lower bound puts `g (f x)` near `x`.
  refine ⟨c * D + c * b, fun x ↦ ?_⟩
  simp only [Function.comp_apply, id_eq]
  grw [dist_comm, hf.coarseAntilipschitzWith x (g (f x)), dist_comm, hD (f x)]
  push_cast
  exact le_rfl

end IsQuasiIsometricEmbedding

/-- A map between pseudometric spaces is a quasi-isometry if and only if it is a quasi-isometric
embedding with quasi-dense range.

[C. Löh, *Geometric Group Theory*][loeh2017], Proposition 5.1.10. -/
theorem isQuasiIsometry_iff_quasiDenseRange :
    IsQuasiIsometry f ↔ IsQuasiIsometricEmbedding f ∧ QuasiDenseRange f := by
  constructor
  · exact fun ⟨hf, g, _, _, c, hc⟩ ↦ ⟨hf, c, fun y ↦ ⟨g y, hc y⟩⟩
  · intro h
    obtain ⟨hf, c, hc⟩ := h
    constructor
    · assumption
    · choose g hg using hc; use g
      have hfg : HasFiniteDist (f ∘ g) id := by use c; simpa
      refine ⟨?_, ?_, ?_⟩
      · exact hf.of_hasFiniteDist_comp_id hfg
      · exact hf.hasFiniteDist_comp_id hfg
      · exact hfg

/-- A surjective bilipschitz map is a quasi-isometry. -/
theorem isQuasiIsometry_of_bilipschitz {K₁ K₂ : ℝ≥0} (hf₁ : AntilipschitzWith K₁ f)
    (hf₂ : LipschitzWith K₂ f) (hf : Function.Surjective f) : IsQuasiIsometry f :=
  isQuasiIsometry_iff_quasiDenseRange.2
    ⟨hf₁.coarseAntilipschitzWith.isQuasiIsometricEmbedding hf₂.coarseLipschitzWith, 0, fun y ↦
      let ⟨x, hx⟩ := hf y
      ⟨x, by simp [hx]⟩⟩

/-- A coarse Lipschitz map with a coarse Lipschitz quasi-inverse is a quasi-isometry: if `f` and
`g` are coarse Lipschitz and both composites have finite distance from the identity, then `f` is a
quasi-isometry.

[C. Druțu, M. Kapovich, *Geometric Group Theory*][drutu2018], Definition 8.10. -/
theorem CoarseLipschitzWith.isQuasiIsometry {g : β → α}
    (hf : CoarseLipschitzWith L₁ C₁ f) (hg : CoarseLipschitzWith L₂ C₂ g)
    (hgf : HasFiniteDist (g ∘ f) id) (hfg : HasFiniteDist (f ∘ g) id) :
    IsQuasiIsometry f := by
  obtain ⟨D, hD⟩ := hgf
  obtain ⟨D', hD'⟩ := hfg
  simp only [Function.comp_apply, id_eq] at hD hD'
  -- `x` and `y` are within `D` of `g (f x)` and `g (f y)`, which `g` keeps close.
  have hlower : CoarseAntilipschitzWith L₂ (C₂ + 2 * D) f := fun x y ↦ by
    grw [dist_triangle4 x (g (f x)) (g (f y)) y, dist_comm x, hD x, hD y, hg (f x) (f y)]
    push_cast
    linarith
  exact isQuasiIsometry_iff_quasiDenseRange.2
    ⟨hlower.isQuasiIsometricEmbedding hf, D', fun y ↦ ⟨g y, hD' y⟩⟩

end Metric
