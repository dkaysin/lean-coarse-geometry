/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
module

public import Mathlib.Order.Filter.Lift
public import Mathlib.Tactic.FunProp

public import Coarse.Basic.Rel

/-!
# Coarse spaces

This file defines coarse spaces using a filter-theoretic approach dual to the standard
entourage-based definition.

## Main definitions

* `CoarseSpace α`: A coarse structure on `α`, given by a filter of *cocontrolled* sets on `α × α`.
* `CoarseSpace.IsCocontrolled s`: The predicate that `s : SetRel α α` is cocontrolled (a member of
  the filter).
* `CoarseSpace.IsControlled s`: The predicate that `s : SetRel α α` is controlled.
* `CoarseSpace.IsCoarselyBounded s`: The predicate that `s : Set α` is bounded (i.e `s ×ˢ s` is
  controlled).
* `IsCoarselyClose f g`: The predicate that two maps `f g : α → β` are close.
* `IsControlledMap f`: The predicate that `f : α → β` sends controlled sets to controlled sets.
* `IsCoarselyProperMap f`: The predicate that `f : α → β` has bounded preimages of bounded sets.
* `IsCoarseMap f`: The structure combining `IsControlledMap` and `IsCoarselyProperMap`.

## Implementation notes

Rather than axiomatizing controlled sets directly (which form an ideal-like structure), we work
with their complements, the *cocontrolled* sets, which form a filter. This approach:

* Gives subset and finite union closure for controlled sets automatically from the filter axioms.
* Expresses the composition axiom (making use of the residual) via:
  `cocontrolled ≤ cocontrolled.lift' (fun s ↦ SetRel.res sᶜ s)`.
  One can recover composition in the presence of the filter axioms.

Copied from `CoarseSpace/Defs.lean` in
<https://github.com/koly777/GeometricGroupTheoryLean>; see `ATTRIBUTION.md`.

## Tags

coarse space, coarse geometry, controlled set, bornologous, proper map
-/

@[expose] public section

open Filter
open scoped SetRel

/-- A coarse space is a generalization of the "large-scale" or "coarse" aspects of a metric space,
capturing the notion of bounded distance without requiring a specific metric. It consists of a
filter on `α × α` called the "cocontrolled" sets, whose complements—the *controlled* sets—satisfy
properties analogous to the reflexivity, symmetry, and triangle inequality of a metric.

The controlled sets form a structure similar to a bornology: they are closed under subsets and
finite unions. -/
class CoarseSpace (α : Type*) where
  /-- The filter of cocontrolled sets in a coarse space. -/
  protected cocontrolled : Filter (α × α)
  /-- The complement of the diagonal is cocontrolled. -/
  protected refl : cocontrolled ≤ 𝓟 (SetRel.id)ᶜ
  /-- If `s ∈ cocontrolled`, then `Prod.swap ⁻¹' s ∈ cocontrolled`. -/
  protected symm : Tendsto Prod.swap cocontrolled cocontrolled
  /-- Composition: if `sᶜ` and `tᶜ` are cocontrolled, so is `(sᶜ ○ tᶜ)ᶜ`.
  Stated dually using the residual. -/
  protected comp : cocontrolled ≤ cocontrolled.lift' (fun s ↦ SetRel.res sᶜ s)

/-- Notation for the cocontrolled filter. -/
scoped[Coarse] notation "𝓒" => CoarseSpace.cocontrolled
scoped[Coarse] notation "𝓒[" c "]" => @CoarseSpace.cocontrolled _ c

variable {α β : Type*}

namespace CoarseSpace

/-- Defining a `CoarseSpace` from a filter basis satisfying coarse-space-like axioms. -/
@[simps! cocontrolled, instance_reducible]
def mkOfBasis (B : FilterBasis (α × α))
    (refl : ∀ r ∈ B, r ⊆ (SetRel.id)ᶜ)
    (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r)
    (comp : ∀ r ∈ B, ∃ t ∈ B, t ⊆ SetRel.res rᶜ r) : CoarseSpace α where
  cocontrolled := B.filter
  refl := le_principal_iff.mpr <| B.mem_filter_iff.mpr
    ⟨_, B.nonempty.some_mem, refl _ B.nonempty.some_mem⟩
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := (B.hasBasis.le_basis_iff <| B.hasBasis.lift' <| compl_anti.res monotone_id).2 comp

/-- Defining a `CoarseSpace` from a set of controlled relations. -/
@[simps! cocontrolled, instance_reducible]
def ofControlled (C : Set (SetRel α α))
    (subset_mem : ∀ s₁ ∈ C, ∀ s₂ ⊆ s₁, s₂ ∈ C)
    (union_mem : ∀ s₁ ∈ C, ∀ s₂ ∈ C, s₁ ∪ s₂ ∈ C)
    (refl_mem : SetRel.id ∈ C)
    (symm_mem : ∀ s ∈ C, Prod.swap ⁻¹' s ∈ C)
    (comp_mem : ∀ s ∈ C, s ○ s ∈ C) : CoarseSpace α where
  cocontrolled := comk (· ∈ C)
    (subset_mem _ refl_mem _ <| Set.empty_subset SetRel.id) subset_mem union_mem
  refl := le_principal_iff.mpr <| compl_mem_comk.mpr <| subset_mem _ refl_mem _ fun _ h ↦ h
  symm := fun s ↦ by
    simp only [mem_comk, mem_map]
    exact fun h ↦ Set.preimage_compl ▸ symm_mem _ h
  comp := le_lift'.mpr fun s hs ↦ mem_comk.mpr <| by
    rw [← compl_compl s, ← SetRel.compl_comp, compl_compl, compl_compl]
    exact comp_mem sᶜ hs

variable [CoarseSpace α]

/-- `IsCocontrolled` is the predicate that `s` is in the filter of cocontrolled sets in the ambient
CoarseSpace on `α`. -/
def IsCocontrolled (s : SetRel α α) : Prop := s ∈ CoarseSpace.cocontrolled

/-- `IsControlled` is the predicate that `s` is controlled if its complement is cocontrolled. -/
def IsControlled (s : SetRel α α) : Prop := IsCocontrolled sᶜ

/-- `IsCoarselyBounded` is the predicate that `s : Set α` is bounded if `s ×ˢ s` is controlled. -/
def IsCoarselyBounded (s : Set α) : Prop := IsControlled (s ×ˢ s)

end CoarseSpace

open CoarseSpace

variable [CoarseSpace α] [CoarseSpace β]

omit [CoarseSpace α] in
/-- Two functions are close to each other if `map f g '' SetRel.id` is a controlled set. -/
def IsCoarselyClose (f g : α → β) : Prop := IsControlled <| .map f g '' SetRel.id

@[inherit_doc]
notation:50 f " =ᶜ " g:50 => IsCoarselyClose f g

open Coarse in
/-- A map `f : α → β` is a *controlled map* if the pullback of the CoarseSpace.cocontrolled
filter under the function `Prod.map f f` is contained in the cocontrolled filter.

Equivalently, the function maps controlled sets to controlled sets. -/
@[fun_prop]
def IsControlledMap (f : α → β) : Prop :=
  (𝓒 : Filter (β × β)).comap (.map f f) ≤ 𝓒

/-- A map `f : α → β` is a *coarsely proper map* if the pullback of the coarsely bounded sets
is coarsely bounded. -/
@[fun_prop]
def IsCoarselyProperMap (f : α → β) : Prop :=
  ∀ s : Set β, IsCoarselyBounded s → IsCoarselyBounded (f⁻¹' s)

/-- A map `f : α → β` between coarse spaces is *coarse* if it is a controlled and coarsely
proper map. -/
@[fun_prop]
structure IsCoarseMap (f : α → β) : Prop where
  /-- A coarse map is controlled. -/
  controlled : IsControlledMap f
  /-- A coarse map is coarsely proper. -/
  proper : IsCoarselyProperMap f

/-! ### Notation for non-standard coarse spaces -/

/-- Notation for `IsCocontrolled` with respect to a non-standard coarse space. -/
scoped[Coarse] notation (name := IsCocontrolled_of) "IsCocontrolled[" c "]" =>
  @CoarseSpace.IsCocontrolled _ c

/-- Notation for `IsControlled` with respect to a non-standard coarse space. -/
scoped[Coarse] notation (name := IsControlled_of) "IsControlled[" c "]" =>
  @CoarseSpace.IsControlled _ c

/-- Notation for `IsCoarselyBounded` with respect to a non-standard coarse space. -/
scoped[Coarse] notation (name := IsCoarselyBounded_of) "IsCoarselyBounded[" c "]" =>
  @CoarseSpace.IsCoarselyBounded _ c
