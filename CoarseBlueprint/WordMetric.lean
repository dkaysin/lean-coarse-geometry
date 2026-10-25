/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Geometry.Group.CayleySimpleGraph
import Coarse.Geometry.Group.WordMetric

/-!
# Blueprint: word metrics

Blueprint nodes for `Coarse/GroupTheory/Generators.lean` and
`Coarse/Geometry/Group/{WordMetric, CayleySimpleGraph}.lean` (milestone M3; copies of open Mathlib
pull requests).
-/

attribute [blueprint "Group.Generators"
  (title := /-- Generating family -/)
  (statement := /-- A \emph{generating family} of a group $G$ indexed by $\iota$ is a map
    $\iota \to G$ whose range generates $G$. -/)]
  Group.Generators

attribute [blueprint "Group.Generators.wordLength"
  (title := /-- Word length -/)
  (statement := /-- The \emph{word length} $|g|_P$ of $g$ is the least length of a word in the
    generators and their inverses whose product is $g$. -/)]
  Group.Generators.wordLength

attribute [blueprint "Group.Generators.groupNorm"
  (title := /-- Word metric -/)
  (statement := /-- The word length is a group norm; the \emph{word metric} is
    $d_P(g, h) = |g^{-1} h|_P$ (L\"oh, Def.~5.2.3). -/)]
  Group.Generators.groupNorm Group.Generators.normedGroup

attribute [blueprint "Group.Generators.cayleySimpleGraph"
  (title := /-- Cayley graph -/)
  (statement := /-- The \emph{Cayley graph} of $P$ has vertex set $G$, with $g$ and $h$
    adjacent when $g \ne h$ and $g^{-1} h$ is a generator or the inverse of one. -/)]
  Group.Generators.cayleySimpleGraph

attribute [blueprint "Group.Generators.dist_cayleySimpleGraph"
  (statement := /-- The graph distance in the Cayley graph is the word metric:
    $d(g, h) = |g^{-1} h|_P$. -/)]
  Group.Generators.dist_cayleySimpleGraph
