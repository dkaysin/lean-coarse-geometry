/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Data.List.Chain

/-!
# Additional lemmas about `List.IsChain`

This file adds `List.IsChain.imp₂`: two `IsChain` hypotheses combine into a third, the analogue of
`List.Pairwise.imp₂`.

## Implementation notes

Copied from mathlib4 PR #45132, where it is added to `Mathlib/Data/List/Chain.lean` as
`List.IsChain.imp_of_isChain`; renamed here after `List.Pairwise.imp₂`, with its argument order.
-/

public section

variable {α : Type*} {R : α → α → Prop}

namespace List

/-- If `IsChain R l` and `IsChain S l`, then `IsChain T l` as soon as `R` and `S` imply `T` on
consecutive pairs. -/
theorem IsChain.imp₂ {S T : α → α → Prop} {l : List α} (H : ∀ a b, R a b → S a b → T a b)
    (hR : IsChain R l) (hS : IsChain S l) : IsChain T l := by
  induction hR with
  | nil => exact .nil
  | singleton => exact .singleton _
  | cons_cons hab _ ih =>
    rw [isChain_cons_cons] at hS ⊢
    exact ⟨H _ _ hab hS.1, ih hS.2⟩

end List
