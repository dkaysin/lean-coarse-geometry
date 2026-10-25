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

* `Metric.isQuasiIsometry_iff_quasiDenseRange`: a map is a quasi-isometry if and only if it is a
  quasi-isometric embedding with quasi-dense range.

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

## Tags

quasi-isometric embedding, quasi-isometry, quasi-isometric, quasi-inverse, quasi-dense,
coarsely dense, coarsely surjective, coarse geometry, geometric group theory
-/

@[expose] public section

open scoped NNReal

namespace Metric

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
  {c b L₁ C₁ L₂ C₂ : ℝ≥0} {f : α → β}

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

variable (c' b' : ℝ≥0) in
/-- (c, b)-quasi-isometric embedding is also (c', b')-quasi-isometric embedding
for c ≤ c' and b ≤ b'. -/
theorem mono (hf : IsQuasiIsometricEmbeddingWith c b f) (hc : c ≤ c') (hb : b ≤ b') :
    IsQuasiIsometricEmbeddingWith c' b' f := {
      coarseLipschitzWith := by
        exact hf.coarseLipschitzWith.mono hc hb
      coarseAntilipschitzWith := by
        exact hf.coarseAntilipschitzWith.mono hc (by gcongr)
    }

/-- A map `f` between pseudometric spaces is a **quasi-isometric embedding** if it is a
`(c, b)`-quasi-isometric embedding for some constants `c` and `b`.
[C. Löh, *Geometric Group Theory*][loeh2017], Definition 5.1.6. -/
def IsQuasiIsometricEmbedding (f : α → β) : Prop :=
  ∃ c b, IsQuasiIsometricEmbeddingWith c b f

namespace IsQuasiIsometricEmbedding

/-- A map that is coarse Lipschitz and coarse antilipschitz, for possibly different constants,
is a quasi-isometric embedding. -/
lemma of_coarseLipschitzWith_of_coarseAntilipschitzWith
    (h₁ : CoarseLipschitzWith L₁ C₁ f) (h₂ : CoarseAntilipschitzWith L₂ C₂ f)
    : ∃ L C: ℝ≥0, IsQuasiIsometricEmbeddingWith L C f := by
  use max (max L₁ L₂) 1, max C₁ C₂
  have hC₂ : C₂ ≤ max (max L₁ L₂) 1 * max C₁ C₂ := by
    have hM : (1 : ℝ≥0) ≤ max (max L₁ L₂) 1 := by simp
    calc C₂ ≤ max C₁ C₂ := by simp
      _ = 1 * max C₁ C₂ := by simp
      _ ≤ max (max L₁ L₂) 1 * max C₁ C₂ := by gcongr
  constructor
  · exact h₁.mono (by simp) (by simp)
  · exact h₂.mono (by simp) (hC₂)

end IsQuasiIsometricEmbedding

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
    (hg : IsQuasiIsometry g) (hf : IsQuasiIsometry f) : IsQuasiIsometry (g ∘ f) :=
  sorry

namespace QuasiIsometric

/-- Every pseudometric space is quasi-isometric to itself. -/
@[refl]
theorem refl (α : Type*) [PseudoMetricSpace α] : QuasiIsometric α α :=
  sorry

/-- Being quasi-isometric is symmetric. -/
@[symm]
theorem symm (h : QuasiIsometric α β) : QuasiIsometric β α :=
  sorry

/-- Being quasi-isometric is transitive. -/
@[trans]
theorem trans {γ : Type*} [PseudoMetricSpace γ] (h₁ : QuasiIsometric α β)
    (h₂ : QuasiIsometric β γ) : QuasiIsometric α γ :=
  sorry

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
  exact of_coarseLipschitzWith_of_coarseAntilipschitzWith h₁ h₂

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

end Metric
