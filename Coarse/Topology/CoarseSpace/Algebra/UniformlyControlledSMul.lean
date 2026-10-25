/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Topology.MetricSpace.IsometricSMul

public import Coarse.Topology.CoarseSpace.Basic
public import Coarse.Topology.CoarseSpace.Metric.Basic

/-!
# Uniformly Controlled Scalar Multiplication

This file defines the typeclass `UniformlyControlledSMul Γ α`, which asserts that the action of
`Γ` on the coarse space `α` is *uniformly controlled*: for every controlled set `E`, the union
`⋃ γ, (Prod.map (γ • ·) (γ • ·)) ⁻¹' E` is again controlled. Equivalently, the group elements
act as controlled maps with a uniform witness: a single cocontrolled set works for all `γ` at once.

## Main Results

* `isControlled_iUnion_preimage_smul`: the union of pullbacks of a controlled set under all
  group translates is controlled.
* `isControlled_iUnion_preimage_smul_iff:` Alternative characterization of
  `UniformlyControlledSMul`: the action is uniformly controlled if and only
  if the union of pullbacks of any controlled set under all group translates
  is again controlled.

* `isControlled_image_of_inv_mul_mem`: if `(f a)⁻¹ * f b` lies in a bounded set whenever
  `(a, b) ∈ E`, then the image `Prod.map f f '' E` is controlled.
## Implementation Notes

In metric geometry, a group acting by isometries preserves controlled sets uniformly:
if `dist a b ≤ r`, then `dist (g • a) (g • b) ≤ r` for *all* `g` simultaneously.
`UniformlyControlledSMul` extracts exactly this uniform property into a coarse space axiom,
dropping the metric and replacing it with the filter-theoretic condition

  `𝓒 ≤ 𝓒.lift' (fun s ↦ ⋂ γ, Prod.map (γ • ·) (γ • ·) ⁻¹' s)`

In terms of controlled sets, this is equivalently the statement that

  ` (⋃ γ : Γ, (Prod.map (γ • ·) (γ • ·)) ⁻¹' s)`

is controlled when `s` is controlled. We work with preimages since it plays nicely with complements,
but note that in the group case this is harmless since `(Prod.map (γ • ·) (γ • ·)) ⁻¹' s` is
equivalent to  `(γ⁻¹, γ⁻¹) • s`, and groups are closed under inversion, so obtaining the translates
`(γ, γ) • s` amounts to simply reindexing.

In any case, the condition says that the union of all translates of `s` by elements of `Γ`
is still controlled i.e the accumulated effect of sliding `s` around by every group element
remains bounded. This is trivial when a group acts by isometries.

Copied from `CoarseSpace/Algebra/UniformlyControlledSMul.lean` in
<https://github.com/koly777/GeometricGroupTheoryLean>; see `ATTRIBUTION.md`.

## Tags

coarse space, uniformly controlled, isometric action, coarse geometry
-/

@[expose] public section

open Set Function Filter
open scoped SetRel Coarse Pointwise

variable {Γ G α β : Type*}

/-! ### Uniformly Controlled Scalar Multiplication -/

/-- An action of `Γ` on a coarse space `α` is *uniformly controlled*
if the cocontrolled filter is below by its lift along the intersection of all translates:

`𝓒 ≤ 𝓒.lift' (fun s ↦ ⋂ γ, Prod.map (γ • ·) (γ • ·) ⁻¹' s)`. -/
class UniformlyControlledSMul (Γ : Type*) (α : Type*) [CoarseSpace α] [SMul Γ α] : Prop where
  uniformly_controlled_smul :
  𝓒 ≤ (𝓒 : Filter (α × α)).lift' (fun s ↦ ⋂ γ : Γ, .map (γ • ·) (γ • ·) ⁻¹' s)

/-- An action of `Γ` on a coarse space `α` is *uniformly controlled* if the cocontrolled filter
is below by its lift along the intersection of all translates:

`𝓒 ≤ 𝓒.lift' (fun s ↦ ⋂ γ, Prod.map (γ +ᵥ ·) (γ +ᵥ ·) ⁻¹' s)`. -/
class UniformlyControlledVAdd (Γ : Type*) (α : Type*) [CoarseSpace α] [VAdd Γ α] : Prop where
  uniformly_controlled_vadd :
  𝓒 ≤ (𝓒 : Filter (α × α)).lift' (fun s ↦ ⋂ γ : Γ, .map (γ +ᵥ ·) (γ +ᵥ ·) ⁻¹' s)

attribute [to_additive] UniformlyControlledSMul
export UniformlyControlledSMul (uniformly_controlled_smul)
export UniformlyControlledVAdd (uniformly_controlled_vadd)

@[to_additive]
theorem isControlled_iUnion_preimage_smul [SMul Γ α] [CoarseSpace α]
    [UniformlyControlledSMul Γ α] {s : SetRel α α} (hs : IsControlled s) :
    IsControlled (⋃ γ : Γ, (Prod.map (γ • ·) (γ • ·)) ⁻¹' s) :=
  show (⋃ γ : Γ, (Prod.map (γ • ·) (γ • ·)) ⁻¹' s)ᶜ ∈ (𝓒 : Filter _) from
    (compl_iUnion _).trans (iInter_congr fun _ ↦ preimage_compl.symm) ▸
      uniformly_controlled_smul (mem_lift' hs)

@[to_additive]
theorem isControlled_iUnion_preimage_smul_iff [SMul Γ α] [CoarseSpace α] :
    (∀ {s}, IsControlled s → IsControlled (⋃ γ : Γ, (Prod.map (γ • · : α → α) (γ • ·)) ⁻¹' s)) ↔
    UniformlyControlledSMul Γ α :=
  ⟨fun h ↦ ⟨le_lift'.mpr fun s hs ↦
    have hsc : IsControlled sᶜ := isControlled_iff.mpr <| (compl_compl s).symm ▸ hs
    (congrArg IsCocontrolled ((compl_iUnion _).trans
    (iInter_congr fun _ ↦ compl_compl _))).mp (h hsc)⟩,
   fun _ _ ↦ isControlled_iUnion_preimage_smul⟩

@[to_additive]
theorem isControlled_image_of_inv_mul_mem [Group G] [CoarseSpace G] [UniformlyControlledSMul G G]
    {f : α → G} {s : SetRel α α} {t : Set G} (ht : IsCoarselyBounded t)
    (h : 1 ∈ t) (hdiff : ∀ {a b}, (a, b) ∈ s → (f a)⁻¹ * f b ∈ t) :
    IsControlled (.map f f '' s) :=
  (isControlled_iUnion_preimage_smul ht).subset
    fun _ ⟨⟨a, b⟩, hab, heq⟩ => heq.subst <| mem_iUnion.mpr ⟨(f a)⁻¹,
      show ((f a)⁻¹ • f a, (f a)⁻¹ • f b) ∈ t ×ˢ t from
        mem_prod.mpr
          ⟨(smul_eq_mul ..).trans (inv_mul_cancel (f a)) ▸ h,
           (smul_eq_mul (α := G) ..) ▸ hdiff hab⟩⟩

@[to_additive]
instance (G : Type*) (α : Type*) [Group G] [PseudoEMetricSpace α] [SMul G α] [IsIsometricSMul G α] :
    UniformlyControlledSMul G α where
  uniformly_controlled_smul := le_lift'.mpr fun _ ⟨r, hr⟩ ↦
    ⟨r, fun p hp ↦
      let ⟨g, hg⟩ := not_forall.mp <| mt mem_iInter.mpr hp
      edist_smul_left g p.1 p.2 ▸ hr _ hg⟩
