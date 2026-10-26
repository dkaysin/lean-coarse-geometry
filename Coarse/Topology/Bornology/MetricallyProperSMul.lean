/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Metrically proper and cobounded actions

An action of `G` on a space `X` with a bornology is *metrically proper* if every bounded set
meets only finitely many of its translates, and *cobounded* if the translates of some bounded set
cover `X`. These are the hypotheses on the action in the Švarc–Milnor lemma; metric properness is
the bornological analogue of `ProperlyDiscontinuousSMul`, with bounded sets in place of compact
sets.

## Main definitions

* `IsMetricallyProperSMul G X`: for every bounded `s : Set X`, the set of `g : G` with
  `g • s ∩ s` nonempty is finite.
* `IsCoboundedSMul G X`: the translates of some bounded set cover `X`.

## Main statements

* `isMetricallyProperSMul_of_properlyDiscontinuousSMul`: a properly discontinuous action on a
  proper metric space is metrically proper.
* `isMetricallyProperSMul_of_finite`, `IsMetricallyProperSMul.subgroup`: actions of finite groups,
  and restrictions of metrically proper actions to subgroups, are metrically proper.
* `IsCoboundedSMul.of_finiteIndex`: a subgroup of finite index of a group acting isometrically and
  coboundedly acts coboundedly.

## Implementation notes

The definitions are stated for `[Bornology X]`, since they use only bounded sets; for a
pseudometric space this is the bornology of metrically bounded sets.

## Tags

metrically proper action, proper action, bornology, geometric group theory
-/

@[expose] public section

open scoped Pointwise

/-- An action of `G` on `X` is **metrically proper** if every bounded set `s` meets only finitely
many of its translates: `{g | (g • s ∩ s).Nonempty}` is finite. -/
@[to_additive /-- An additive action of `G` on `X` is **metrically proper** if every bounded set
`s` meets only finitely many of its translates: `{g | (g +ᵥ s ∩ s).Nonempty}` is finite. -/]
def IsMetricallyProperSMul (G X : Type*) [SMul G X] [Bornology X] : Prop :=
  ∀ s : Set X, Bornology.IsBounded s → {g : G | (g • s ∩ s).Nonempty}.Finite

/-- An action of `G` on `X` is **cobounded** if the translates of some bounded set cover `X`. -/
@[to_additive /-- An additive action of `G` on `X` is **cobounded** if the translates of some
bounded set cover `X`. -/]
def IsCoboundedSMul (G X : Type*) [SMul G X] [Bornology X] : Prop :=
  ∃ s : Set X, Bornology.IsBounded s ∧ ⋃ g : G, g • s = Set.univ

/-- A properly discontinuous action on a proper metric space is metrically proper: bounded sets
have compact closures. -/
@[to_additive /-- A properly discontinuous additive action on a proper metric space is metrically
proper. -/]
theorem isMetricallyProperSMul_of_properlyDiscontinuousSMul {G X : Type*} [SMul G X]
    [PseudoMetricSpace X] [ProperSpace X] [ProperlyDiscontinuousSMul G X] :
    IsMetricallyProperSMul G X := fun _s hs ↦
  (ProperlyDiscontinuousSMul.finite_disjoint_inter_image hs.isCompact_closure
    hs.isCompact_closure).subset fun _g ⟨x, hx, hx'⟩ ↦
      ⟨x, Set.smul_set_mono subset_closure hx, subset_closure hx'⟩

/-- Every action of a finite group is metrically proper. -/
@[to_additive /-- Every additive action of a finite group is metrically proper. -/]
theorem isMetricallyProperSMul_of_finite {G X : Type*} [Finite G] [SMul G X] [Bornology X] :
    IsMetricallyProperSMul G X :=
  fun _ _ ↦ Set.toFinite _

/-- The restriction of a metrically proper action to a subgroup is metrically proper. -/
@[to_additive /-- The restriction of a metrically proper additive action to a subgroup is
metrically proper. -/]
theorem IsMetricallyProperSMul.subgroup {G X : Type*} [Group G] [MulAction G X] [Bornology X]
    (h : IsMetricallyProperSMul G X) (H : Subgroup G) : IsMetricallyProperSMul H X :=
  fun s hs ↦ (h s hs).preimage Subtype.val_injective.injOn

/-- The restriction of an isometric action to a subgroup is isometric. -/
@[to_additive /-- The restriction of an isometric additive action to a subgroup is isometric. -/]
instance Subgroup.isIsometricSMul {G X : Type*} [Group G] [PseudoEMetricSpace X] [MulAction G X]
    [IsIsometricSMul G X] (H : Subgroup G) : IsIsometricSMul H X :=
  ⟨fun h ↦ isometry_smul X (h : G)⟩

/-- If `G` acts isometrically and coboundedly, then so does every subgroup of finite index. -/
@[to_additive /-- If `G` acts isometrically and coboundedly by translations, then so does every
subgroup of finite index. -/]
theorem IsCoboundedSMul.of_finiteIndex {G X : Type*} [Group G] [PseudoMetricSpace X]
    [MulAction G X] [IsIsometricSMul G X] (h : IsCoboundedSMul G X) (H : Subgroup G)
    [H.FiniteIndex] : IsCoboundedSMul H X := by
  obtain ⟨s, hs, hcov⟩ := h
  refine ⟨⋃ q : G ⧸ H, q.out⁻¹ • s, Bornology.isBounded_iUnion.2 fun q ↦ hs.smul _,
    Set.eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨g, hg⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ x)
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g⁻¹
  refine Set.mem_iUnion.2 ⟨k, Set.mem_smul_set.2
    ⟨(k : G)⁻¹ • x, Set.mem_iUnion.2 ⟨(g⁻¹ : G), ?_⟩, ?_⟩⟩
  · rw [hk, mul_inv_rev, inv_inv, mul_smul, Set.smul_mem_smul_set_iff]
    exact hg
  · simp [Subgroup.smul_def]
