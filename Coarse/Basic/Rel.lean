/-
Copyright (c) 2026 Saif Ghobash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saif Ghobash
-/
module

public import Mathlib.Basic.Rel

/-!
# Residuals of relations

This file defines the residual `R.res S` of relations and proves basic lemmas about it.

## Implementation notes

Copied from `ForMathlib/Data/Rel.lean` in
<https://github.com/koly777/GeometricGroupTheoryLean>; see `ATTRIBUTION.md`.
-/

@[expose] public section

variable {α β γ : Type*}

namespace SetRel

/-- The residual `R.res S` where `x ~[R.res S] z` iff every `R`-successor of `x`
is an `S`-predecessor of `z`. -/
def res (R : SetRel α β) (S : SetRel β γ) : SetRel α γ :=
  {p | ∀ y, p.1 ~[R] y → y ~[S] p.2}

variable {R : SetRel α β} {S : SetRel β γ}

@[simp]
theorem mem_res {x z} : x ~[R.res S] z ↔ ∀ y, x ~[R] y → y ~[S] z := .rfl

theorem compl_comp : (R ○ S)ᶜ = R.res Sᶜ :=
  Set.ext fun _ ↦ not_exists.trans <| forall_congr' fun _ ↦
    not_and.trans <| imp_congr_right fun _ ↦ .rfl

theorem iterate_res_compl (s : SetRel α α) (n : ℕ) :
    (s.res ·)^[n] sᶜ = ((s ○ ·)^[n] s)ᶜ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, SetRel.compl_comp]

end SetRel

theorem Antitone.res {ι : Type*} [Preorder ι] {f : ι → SetRel α β} {g : ι → SetRel β γ}
    (hf : Antitone f) (hg : Monotone g) : Monotone (fun s ↦ (f s).res (g s)) :=
  fun _ _ h _ hr y hy ↦ hg h (hr y (hf h hy))
