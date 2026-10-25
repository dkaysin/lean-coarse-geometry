/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Topology.Bornology.Basic

/-!
# Metrically proper actions

An action of `G` on a space `X` with a bornology is *metrically proper* if every bounded set
meets only finitely many of its translates. This is the hypothesis on the action in the
Švarc–Milnor lemma; it is the bornological analogue of `ProperlyDiscontinuousSMul`, with bounded
sets in place of compact sets.

## Main definitions

* `IsMetricallyProperSMul G X`: for every bounded `s : Set X`, the set of `g : G` with
  `g • s ∩ s` nonempty is finite.

## Implementation notes

The definition is stated for `[Bornology X]`, since it uses only bounded sets; for a pseudometric
space this is the bornology of metrically bounded sets.

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
