/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Distances along shortest walks

A walk whose length is the distance between its endpoints is shortest between any two of its
vertices.

## Main statements

* `SimpleGraph.Walk.dist_getVert_of_length_eq_dist`: along a walk `p` of length `G.dist u v`, the
  vertices at positions `i ≤ j` are at distance `j - i`.

## Tags

graph distance, shortest walk, geodesic walk
-/

@[expose] public section

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Along a walk `p` of length `G.dist u v`, the vertices at positions `i ≤ j ≤ p.length` are at
distance `j - i`. -/
theorem dist_getVert_of_length_eq_dist {p : G.Walk u v} (hp : p.length = G.dist u v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) : G.dist (p.getVert i) (p.getVert j) = j - i := by
  -- The subwalk from position `i` to position `j` is again a shortest walk.
  have h := length_eq_dist_of_subwalk hp ((isSubwalk_take (p.drop i) (j - i)).trans
    (isSubwalk_drop p i))
  rw [take_length, drop_length, drop_getVert, Nat.add_sub_cancel' hij] at h
  omega

end SimpleGraph.Walk
