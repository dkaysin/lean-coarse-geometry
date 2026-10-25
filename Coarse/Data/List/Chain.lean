/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Data.List.Chain

/-!
# Additional lemmas about `List.IsChain`

This file adds `List.IsChain.imp_of_isChain`: an `IsChain` hypothesis transfers to another
relation along the consecutive pairs of a list that are related by a third relation.

## Implementation notes

Copied from mathlib4 PR #45132, where it is added to `Mathlib/Data/List/Chain.lean`.
-/

public section

variable {α : Type*} {R : α → α → Prop}

namespace List

/-- If consecutive elements of `l` are related by `T`, then `IsChain R l` implies `IsChain S l` as
soon as `R` implies `S` on `T`-related pairs. -/
theorem IsChain.imp_of_isChain {S T : α → α → Prop} {l : List α} (hT : IsChain T l)
    (H : ∀ a b, T a b → R a b → S a b) (hR : IsChain R l) : IsChain S l := by
  induction hT with
  | nil => exact .nil
  | singleton => exact .singleton _
  | cons_cons hab _ ih =>
    rw [isChain_cons_cons] at hR ⊢
    exact ⟨H _ _ hab hR.1, ih hR.2⟩

end List
