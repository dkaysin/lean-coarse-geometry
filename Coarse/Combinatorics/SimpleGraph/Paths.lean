/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Non-backtracking walks

A walk is non-backtracking if it never traverses an edge and then immediately traverses the same
edge back.

## Main definitions

- `SimpleGraph.Walk.IsNonBacktracking`: no dart of the walk is followed by its reverse.

## Implementation notes

Copied from mathlib4 PR #45132, where it is added to
`Mathlib/Combinatorics/SimpleGraph/Paths.lean`.
-/

@[expose] public section

universe u

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-! ## Non-backtracking walks -/

namespace Walk

variable {G}

/-- A walk is *non-backtracking* if it never traverses an edge and then immediately traverses the
same edge back, i.e. no dart of the walk is followed by its reverse. -/
@[mk_iff isNonBacktracking_def]
structure IsNonBacktracking {u v : V} (p : G.Walk u v) : Prop where
  isChain_darts : p.darts.IsChain (fun d d' ↦ d ≠ d'.symm)

/-- A trail has no repeated edges, so in particular it does not backtrack. -/
theorem IsTrail.isNonBacktracking {u v : V} {p : G.Walk u v} (h : p.IsTrail) :
    p.IsNonBacktracking := by
  have hedges : p.edges.IsChain (· ≠ ·) := h.edges_nodup.isChain
  rw [edges_eq_map_darts, List.isChain_map] at hedges
  refine ⟨hedges.imp ?_⟩
  intro d d' hne hsymm
  apply hne
  rw [hsymm, Dart.edge_symm]

/-- A path does not backtrack. -/
theorem IsPath.isNonBacktracking {u v : V} {p : G.Walk u v} (h : p.IsPath) :
    p.IsNonBacktracking :=
  h.isTrail.isNonBacktracking

@[simp]
theorem isNonBacktracking_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsNonBacktracking ↔ p.IsNonBacktracking := by
  subst_vars
  rfl

@[simp]
theorem IsNonBacktracking.nil {u : V} : (nil : G.Walk u u).IsNonBacktracking :=
  ⟨by simp⟩

@[simp]
theorem isNonBacktracking_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsNonBacktracking ↔ p.IsNonBacktracking ∧ p.snd ≠ u := by
  rw [isNonBacktracking_def, isNonBacktracking_def, darts_cons, List.isChain_cons, and_comm]
  apply and_congr_right
  intro _
  cases p with
  | nil => simp [h.ne.symm]
  | cons h' q => simp [eq_comm]

@[simp]
theorem isNonBacktracking_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.IsNonBacktracking ↔ p.IsNonBacktracking := by
  rw [isNonBacktracking_def, isNonBacktracking_def, darts_reverse, List.isChain_reverse,
    List.isChain_map]
  simp_rw [Dart.symm_symm]
  exact ⟨fun h ↦ h.imp fun _ _ ↦ Ne.symm, fun h ↦ h.imp fun _ _ ↦ Ne.symm⟩

end Walk

end SimpleGraph
