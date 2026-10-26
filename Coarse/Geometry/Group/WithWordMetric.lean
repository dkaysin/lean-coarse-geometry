/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Coarse.Geometry.Group.WordMetric
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# A group with the word metric of a generating family

`Group.Generators.WithWordMetric P` is a copy of the group `G` that carries the word metric of
the generating family `P` as an instance. The word metrics of different generating families live
on different types, so that maps between them are stated without passing instances explicitly.

## Main definitions

* `Group.Generators.WithWordMetric P`: the group `G` with the word metric of `P`, with the maps
  `toWordMetric P : G → P.WithWordMetric` and `ofWordMetric : P.WithWordMetric → G`.
* `Group.Generators.WithWordMetric.mulEquiv P`: the group isomorphism `P.WithWordMetric ≃* G`.
* `Group.Generators.WithWordMetric.congr P Q`: the identity of `G`, from the word metric of `P` to
  the word metric of `Q`.
* The action of `G` on `P.WithWordMetric` by left multiplication, which is isometric.
* `AddGroup.Generators.WithWordMetric P`, `AddGroup.Generators.WithWordMetric.addEquiv P`,
  `AddGroup.Generators.WithWordMetric.congr P Q`: the additive versions of the above.

## Implementation notes

As `WithAbs` and `WithLp` in Mathlib, `WithWordMetric P` is a one-field structure, not a type
synonym, so that `G` and `P.WithWordMetric` are not identified by unfolding.

## Tags

word metric, generating family, type synonym
-/

@[expose] public section

/-- The additive group `G` with the word metric of the generating family `P`. -/
structure AddGroup.Generators.WithWordMetric {G ι : Type*} [AddGroup G]
    (P : AddGroup.Generators G ι) where
  /-- An element of `G`, as an element of `P.WithWordMetric`. -/
  toWordMetric (P) ::
  /-- An element of `P.WithWordMetric`, as an element of `G`. -/
  ofWordMetric : G

namespace Group.Generators

variable {G ι κ : Type*} [Group G]

/-- The group `G` with the word metric of the generating family `P`. -/
structure WithWordMetric (P : Generators G ι) where
  /-- An element of `G`, as an element of `P.WithWordMetric`. -/
  toWordMetric (P) ::
  /-- An element of `P.WithWordMetric`, as an element of `G`. -/
  ofWordMetric : G

attribute [to_additive] WithWordMetric

namespace WithWordMetric

variable (P : Generators G ι) (Q : Generators G κ)

@[to_additive (attr := simp)]
lemma ofWordMetric_toWordMetric (g : G) : ofWordMetric (toWordMetric P g) = g := rfl

@[to_additive (attr := simp)]
lemma toWordMetric_ofWordMetric (x : P.WithWordMetric) : toWordMetric P (ofWordMetric x) = x :=
  rfl

/-- The bijection between `P.WithWordMetric` and `G`. -/
@[to_additive /-- The bijection between `P.WithWordMetric` and `G`. -/]
def equiv : P.WithWordMetric ≃ G where
  toFun := ofWordMetric
  invFun := toWordMetric P
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive]
instance : Group P.WithWordMetric := (equiv P).group

/-- The group isomorphism between `P.WithWordMetric` and `G`. -/
@[to_additive /-- The group isomorphism between `P.WithWordMetric` and `G`. -/]
def mulEquiv : P.WithWordMetric ≃* G where
  __ := equiv P
  map_mul' _ _ := rfl

@[to_additive]
noncomputable instance : NormedGroup P.WithWordMetric :=
  letI := P.normedGroup
  NormedGroup.induced _ _ (mulEquiv P) (equiv P).injective

/-- The distance between `x` and `y` is the word length of `x⁻¹ * y`. -/
@[to_additive /-- The distance between `x` and `y` is the word length of `-x + y`. -/]
lemma dist_eq (x y : P.WithWordMetric) :
    dist x y = P.wordLength ((ofWordMetric x)⁻¹ * ofWordMetric y) :=
  rfl

/-- `G` acts on `P.WithWordMetric` by left multiplication. -/
@[to_additive /-- `G` acts on `P.WithWordMetric` by left addition. -/]
instance : MulAction G P.WithWordMetric where
  smul g x := toWordMetric P (g * ofWordMetric x)
  one_smul x := congrArg (toWordMetric P) (one_mul (ofWordMetric x))
  mul_smul g h x := congrArg (toWordMetric P) (mul_assoc g h (ofWordMetric x))

@[to_additive (attr := simp)]
lemma ofWordMetric_smul (g : G) (x : P.WithWordMetric) :
    ofWordMetric (g • x) = g * ofWordMetric x :=
  rfl

/-- The word metric is invariant under left multiplication. -/
@[to_additive /-- The word metric is invariant under left addition. -/]
instance : IsIsometricSMul G P.WithWordMetric :=
  ⟨fun g ↦ Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq, dist_eq, ofWordMetric_smul, ofWordMetric_smul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left]⟩

/-- The identity of `G`, from the word metric of `P` to the word metric of `Q`. -/
@[to_additive
/-- The identity of `G`, from the word metric of `P` to the word metric of `Q`. -/]
def congr : P.WithWordMetric ≃* Q.WithWordMetric := (mulEquiv P).trans (mulEquiv Q).symm

@[to_additive (attr := simp)]
lemma ofWordMetric_congr (x : P.WithWordMetric) : ofWordMetric (congr P Q x) = ofWordMetric x :=
  rfl

end WithWordMetric

end Group.Generators
