/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
module

public import Coarse.Topology.CoarseSpace.Basic

/-!
# Coarse equivalences

A `CoarseEquiv X Y` consists of controlled maps `f : X → Y` and `g : Y → X` such that
`f ∘ g` and `g ∘ f` are close to the identity. We write `X ≃ᶜ Y`.

## Main definitions

* `CoarseEquiv α β`, notation `α ≃ᶜ β`: a coarse equivalence between `α` and `β`.
* `CoarseEquiv.refl`, `CoarseEquiv.symm`, `CoarseEquiv.trans`: identity, inverse and composition.
* `CoarseEquiv.ofEquiv`: the coarse equivalence given by an equivalence that is controlled in
  both directions.

## Implementation notes

Copied from `CoarseSpace/CoarseEquiv/Defs.lean` in
<https://github.com/koly777/GeometricGroupTheoryLean>; see `ATTRIBUTION.md`.
-/

@[expose] public section

open Function Filter
open scoped SetRel Coarse

variable {α β γ : Type*}

/-- Coarse equivalence between `α` and `β`. -/
structure CoarseEquiv (α β : Type*) [CoarseSpace α] [CoarseSpace β] where
  /-- The forward map. -/
  toFun : α → β
  /-- The inverse map. -/
  invFun : β → α
  /-- The forward map is controlled. -/
  controlled_toFun : IsControlledMap toFun := by fun_prop
  /-- The inverse map is controlled. -/
  controlled_invFun : IsControlledMap invFun := by fun_prop
  /-- The forward map followed by the inverse map is close to the identity. -/
  isCoarselyClose_id_right : toFun ∘ invFun =ᶜ id
  /-- The inverse map followed by the forward map is close to the identity. -/
  isCoarselyClose_id_left : invFun ∘ toFun =ᶜ id

@[inherit_doc]
infixl:25 " ≃ᶜ " => CoarseEquiv

namespace CoarseEquiv

variable [CoarseSpace α] [CoarseSpace β] [CoarseSpace γ]

/-- The forward map of a coarse equivalence is a coarse map. -/
@[fun_prop]
protected theorem isCoarseMap (e : α ≃ᶜ β) : IsCoarseMap e.toFun :=
  ⟨e.controlled_toFun, e.controlled_invFun.isCoarselyProperMap_of_isCoarselyClose_comp_id
    e.isCoarselyClose_id_left⟩

instance : CoeFun (α ≃ᶜ β) (fun _ ↦ α → β) := ⟨fun e ↦ e.toFun⟩

@[simp] theorem coe_toFun (e : α ≃ᶜ β) : (e.toFun : α → β) = e := rfl

@[ext]
theorem ext {e₁ e₂ : α ≃ᶜ β} (h : ∀ x, e₁ x = e₂ x) (h' : ∀ y, e₁.invFun y = e₂.invFun y) :
    e₁ = e₂ := by
  cases e₁; cases e₂; simp only [mk.injEq]; exact ⟨funext h, funext h'⟩

/-- Identity coarse equivalence. -/
@[simps! -fullyApplied toFun invFun]
protected def refl (α : Type*) [CoarseSpace α] : α ≃ᶜ α where
  toFun := id
  invFun := id
  isCoarselyClose_id_left := IsCoarselyClose.refl _
  isCoarselyClose_id_right := IsCoarselyClose.refl _

/-- Inverse coarse equivalence. -/
@[symm]
protected def symm (e : α ≃ᶜ β) : β ≃ᶜ α where
  toFun := e.invFun
  invFun := e.toFun
  controlled_toFun := e.controlled_invFun
  controlled_invFun := e.controlled_toFun
  isCoarselyClose_id_left := e.isCoarselyClose_id_right
  isCoarselyClose_id_right := e.isCoarselyClose_id_left

@[fun_prop]
protected theorem isCoarseMap_symm (e : α ≃ᶜ β) : IsCoarseMap e.symm.toFun :=
  ⟨e.controlled_invFun, e.controlled_toFun.isCoarselyProperMap_of_isCoarselyClose_comp_id
    e.isCoarselyClose_id_right⟩

@[simp] theorem coe_invFun (e : α ≃ᶜ β) : (e.invFun : β → α) = e.symm := rfl
@[simp] theorem symm_symm (e : α ≃ᶜ β) : e.symm.symm = e := by cases e; rfl

@[fun_prop]
theorem controlled_toFun' (e : α ≃ᶜ β) : IsControlledMap e.toFun := e.controlled_toFun

@[fun_prop]
theorem controlled_invFun' (e : α ≃ᶜ β) : IsControlledMap e.invFun := e.controlled_invFun

/-- Composition of coarse equivalences. -/
@[trans]
protected def trans (e₁ : α ≃ᶜ β) (e₂ : β ≃ᶜ γ) : α ≃ᶜ γ where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  isCoarselyClose_id_right :=
    ((e₁.isCoarselyClose_id_right.comp e₂.invFun).lcomp e₂.controlled_toFun).trans
      e₂.isCoarselyClose_id_right
  isCoarselyClose_id_left :=
    ((e₂.isCoarselyClose_id_left.comp e₁.toFun).lcomp e₁.controlled_invFun).trans
      e₁.isCoarselyClose_id_left

@[simp] theorem trans_apply (e₁ : α ≃ᶜ β) (e₂ : β ≃ᶜ γ) (x : α) : (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] theorem symm_trans (e₁ : α ≃ᶜ β) (e₂ : β ≃ᶜ γ) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := rfl

/-- Construct a coarse equivalence from an equivalence where both directions are coarse. -/
def ofEquiv (e : α ≃ β)
    (hf : IsControlledMap e := by fun_prop)
    (hg : IsControlledMap e.symm := by fun_prop) :
    α ≃ᶜ β where
  toFun := e
  invFun := e.symm
  isCoarselyClose_id_right := (Equiv.self_comp_symm e) ▸ (IsCoarselyClose.refl _)
  isCoarselyClose_id_left := (Equiv.symm_comp_self e) ▸ (IsCoarselyClose.refl _)

end CoarseEquiv
