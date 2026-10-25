/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
module

public import Mathlib.Order.Filter.Lift
public import Coarse.Topology.CoarseSpace.Defs

/-!
# Basic properties of coarse spaces

This file develops the fundamental API for coarse spaces, establishing that controlled sets form
a coarse structure (closed under subsets, finite unions, inverses, and compositions), that
closeness is an equivalence relation on maps, and that coarse maps compose.

## Main statements

* `CoarseSpace.IsControlled.subset`, `.union`, `.inv`, `.comp`: controlled sets form a coarse
  structure.
* `CoarseSpace.IsCoarselyBounded.subset`, `.union_of_nonempty_inter`: coarsely bounded sets are
  closed under subsets and unions with nonempty intersection.
* `CoarseSpace.IsControlled.isCoarselyBounded_ball`: balls of controlled sets are coarsely
  bounded.
* `IsCoarselyClose.refl`, `.symm`, `.trans`: closeness is an equivalence relation.
* `IsCoarselyClose.isControlledMap`: a map close to a controlled map is controlled.
* `isCoarseMap_id`, `IsCoarseMap.comp`: coarse maps are closed under identity and composition.
* `IsControlledMap.isCoarselyProperMap_of_isCoarselyClose_comp_id`: a map with a controlled left
  inverse close to the identity is coarsely proper.

## Implementation notes

Copied from `CoarseSpace/Basic.lean` in
<https://github.com/koly777/GeometricGroupTheoryLean>; see `ATTRIBUTION.md`.
-/

@[expose] public section

open Set SetRel Function Filter CoarseSpace
open scoped SetRel Coarse

variable {α β γ : Type*}

@[ext]
protected theorem CoarseSpace.ext {c₁ c₂ : CoarseSpace α}
    (h : c₁.cocontrolled = c₂.cocontrolled) : c₁ = c₂ := by
  cases c₁; cases c₂; congr

namespace CoarseSpace

/-! ### Controlled sets -/

section IsControlled

variable [CoarseSpace α] {s t : SetRel α α}

theorem isControlled_iff : IsControlled s ↔ IsCocontrolled sᶜ := .rfl

@[simp] theorem isControlled_id : IsControlled (SetRel.id : SetRel α α) :=
  le_principal_iff.mp CoarseSpace.refl

@[simp] theorem isControlled_empty : IsControlled (∅ : SetRel α α) :=
  isControlled_iff.mpr <| compl_empty ▸ univ_mem

theorem IsControlled.subset (ht : IsControlled t) (h : s ⊆ t) : IsControlled s :=
  mem_of_superset ht <| compl_subset_compl_of_subset h

theorem IsControlled.union (hs : IsControlled s) (ht : IsControlled t) :
    IsControlled (s ∪ t) := by
  rw [isControlled_iff, IsCocontrolled, compl_union]
  exact inter_mem hs ht

theorem IsControlled.inv (hs : IsControlled s) : IsControlled s.inv := CoarseSpace.symm hs

theorem IsControlled.comp (hs : IsControlled s) (ht : IsControlled t) :
    IsControlled (s ○ t) := by
  have h := CoarseSpace.comp (mem_lift' (inter_mem hs ht))
  rw [isControlled_iff, IsCocontrolled, SetRel.compl_comp]
  exact mem_of_superset h fun p hp y hy ↦ (hp y fun h ↦ h.1 hy).2

theorem IsControlled.iterate_comp (hs : IsControlled s) (ht : IsControlled t) :
    ∀ n, IsControlled ((s ○ ·)^[n] t)
  | 0 => ht
  | n + 1 => iterate_succ_apply' (s ○ ·) n t ▸ hs.comp (iterate_comp hs ht n)

section ofControlled

variable {s : SetRel α α}

omit [CoarseSpace α]

theorem isCocontrolled_ofControlled_iff (C : Set (SetRel α α))
    {subset_mem union_mem refl_mem symm_mem comp_mem} :
    IsCocontrolled[CoarseSpace.ofControlled C
      subset_mem union_mem refl_mem symm_mem comp_mem] s ↔ sᶜ ∈ C := .rfl

theorem isControlled_ofControlled_iff (C : Set (SetRel α α))
    {subset_mem union_mem refl_mem symm_mem comp_mem} :
    IsControlled[CoarseSpace.ofControlled C
      subset_mem union_mem refl_mem symm_mem comp_mem] s ↔ s ∈ C := by
  rw [@isControlled_iff, isCocontrolled_ofControlled_iff, compl_compl]

end ofControlled

end IsControlled

/-! ### Coarsely bounded sets -/

section IsCoarselyBounded

variable [CoarseSpace α] {s t : Set α}

theorem isCoarselyBounded_iff : IsCoarselyBounded s ↔ IsControlled (s ×ˢ s) := .rfl

@[simp] theorem isCoarselyBounded_singleton (x : α) : IsCoarselyBounded ({x} : Set α) :=
  isControlled_id.subset fun _ ⟨ha, hb⟩ ↦ ha.trans hb.symm

@[simp] theorem isCoarselyBounded_empty : IsCoarselyBounded (∅ : Set α) :=
  isCoarselyBounded_iff.mpr <| prod_empty ▸ isControlled_empty

theorem IsCoarselyBounded.subset (hs : IsCoarselyBounded s) (ht : t ⊆ s) : IsCoarselyBounded t :=
  IsControlled.subset hs (prod_mono ht ht)

theorem IsCoarselyBounded.union_of_nonempty_inter (hs : IsCoarselyBounded s)
    (ht : IsCoarselyBounded t) (hst : (s ∩ t).Nonempty) : IsCoarselyBounded (s ∪ t) :=
  let ⟨x, hxs, hxt⟩ := hst
  ((hs.union ht).comp (hs.union ht)).subset fun _ ⟨ha, hb⟩ ↦
    ⟨x, ha.elim (fun has ↦ .inl ⟨has, hxs⟩) (fun hat ↦ .inr ⟨hat, hxt⟩),
        hb.elim (fun hbs ↦ .inl ⟨hxs, hbs⟩) (fun hbt ↦ .inr ⟨hxt, hbt⟩)⟩

theorem IsControlled.isCoarselyBounded_ball {R : SetRel α α} (hR : IsControlled R) (x₀ : α) :
    IsCoarselyBounded (R.ball x₀) :=
  (hR.comp hR.inv).subset fun ⟨_, _⟩ ⟨h₁, h₂⟩ ↦ ⟨x₀, h₁, h₂⟩

end IsCoarselyBounded

end CoarseSpace

/-! ### Closeness of maps -/

section IsCoarselyClose

variable [CoarseSpace β]

@[refl]
theorem IsCoarselyClose.refl (f : α → β) : f =ᶜ f :=
  isControlled_id.subset fun _ ⟨_, ⟨h, hf⟩⟩ ↦ hf ▸ congrArg f h

@[symm]
theorem IsCoarselyClose.symm {f g : α → β} (h : f =ᶜ g) : g =ᶜ f :=
  h.inv.subset fun _ ⟨⟨x, y⟩, ⟨h, h₁⟩⟩ ↦ ⟨(x, y), ⟨h, h₁ ▸ h ▸ rfl⟩⟩

@[trans]
theorem IsCoarselyClose.trans {f g h : α → β} (hfg : f =ᶜ g) (hgh : g =ᶜ h) : f =ᶜ h :=
  (hfg.comp hgh).subset fun _ ⟨⟨x, _⟩, hxy, hf⟩ ↦
    hf ▸ ⟨g x, ⟨(x, x), rfl, rfl⟩, ⟨(x, x), rfl, hxy ▸ rfl⟩⟩

theorem IsCoarselyClose.comp {f g : α → β} (h : γ → α) (hfg : f =ᶜ g) : f ∘ h =ᶜ g ∘ h :=
  hfg.subset fun _ ⟨x, hx, hf⟩ ↦ ⟨(h x.1, h x.2), congrArg h hx, hf⟩

theorem IsCoarselyClose.lcomp [CoarseSpace γ] {f g : α → β} (hfg : f =ᶜ g) {h : β → γ}
    (hh : IsControlledMap h) : h ∘ f =ᶜ h ∘ g :=
  let ⟨_, ht, hts⟩ := hh hfg
  mem_of_superset ht fun _ hxy ⟨p, hp, hfp⟩ ↦
    hts (mem_preimage.mpr <| mem_of_eq_of_mem (hfp ▸ rfl) hxy) ⟨p, hp, rfl⟩

end IsCoarselyClose

/-! ### Coarse maps -/

section Maps

variable [CoarseSpace α] [CoarseSpace β] [CoarseSpace γ]
variable {f : α → β} {g : β → γ}

theorem isControlledMap_iff :
    IsControlledMap f ↔ ∀ s : SetRel α α, IsControlled s → IsControlled (Prod.map f f '' s) := by
  refine ⟨fun hf s hs ↦ compl_mem_comap.mp (hf hs), fun hf t ht ↦ ?_⟩
  rw [mem_comap_iff_compl]
  exact hf tᶜ (by rw [isControlled_iff, compl_compl]; exact ht)

@[fun_prop]
theorem isControlledMap_id : IsControlledMap (id : α → α) := comap_id.le

@[fun_prop]
theorem IsControlledMap.comp (hg : IsControlledMap g) (hf : IsControlledMap f) :
    IsControlledMap (g ∘ f) :=
  show comap _ _ ≤ _ from
    (Prod.map_comp_map f f g g).symm ▸ comap_comap.symm ▸ (comap_mono hg).trans hf

theorem IsControlledMap.isCoarselyBounded_image {s : Set α} (hg : IsControlledMap f)
    (hs : IsCoarselyBounded s) : IsCoarselyBounded (f '' s) :=
  (congrArg IsControlled (prodMap_image_prod f f s s)).mp (isControlledMap_iff.1 hg _ hs)

theorem IsControlledMap.isCoarselyProperMap_of_isCoarselyClose_comp_id
    {f : β → α} (hf : IsControlledMap f)
    {g : α → β} (hfg : f ∘ g =ᶜ (id : α → α)) :
    IsCoarselyProperMap g := fun _ h ↦
  (hfg.inv.comp (hf.isCoarselyBounded_image h) |>.comp hfg).subset
    fun ⟨x, y⟩ ⟨hx, hy⟩ ↦
      ⟨f (g y), ⟨f (g x), ⟨(x, x), rfl, rfl⟩, mk_mem_prod ⟨g x, hx, rfl⟩ ⟨g y, hy, rfl⟩⟩,
        ⟨(y, y), rfl, rfl⟩⟩

theorem IsCoarselyClose.isControlledMap {f g : α → β}
    (hfg : f =ᶜ g) (hg : IsControlledMap g) :
    IsControlledMap f := isControlledMap_iff.2 fun s hs ↦
  let hgs := isControlledMap_iff.1 hg s hs
  ((IsControlled.comp hfg hgs).comp hfg.inv).subset
    fun _ ⟨p, hps, hp⟩ ↦ hp ▸
      ⟨g p.2, ⟨g p.1, ⟨(p.1, p.1), rfl, rfl⟩, ⟨p, hps, rfl⟩⟩, ⟨(p.2, p.2), rfl, rfl⟩⟩

theorem isCoarselyProperMap_id : IsCoarselyProperMap (id : α → α) := fun _ hs ↦ hs

theorem IsCoarselyProperMap.comp (hg : IsCoarselyProperMap g) (hf : IsCoarselyProperMap f) :
    IsCoarselyProperMap (g ∘ f) := fun s hs ↦ hf _ (hg s hs)

@[fun_prop]
theorem isCoarseMap_id : IsCoarseMap (id : α → α) := ⟨isControlledMap_id, isCoarselyProperMap_id⟩

@[fun_prop]
theorem IsCoarseMap.comp (hg : IsCoarseMap g) (hf : IsCoarseMap f) : IsCoarseMap (g ∘ f) :=
  ⟨hg.controlled.comp hf.controlled, hg.proper.comp hf.proper⟩

end Maps
