/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Geometry.Group.CayleySimpleGraph
import Coarse.Geometry.Group.WordMetric
import Coarse.Geometry.Group.WordMetricBounds

/-!
# Blueprint: word metrics

Blueprint nodes for `Coarse/GroupTheory/Generators.lean` and
`Coarse/Geometry/Group/{WordMetric, CayleySimpleGraph}.lean` (milestone M3; copies of open Mathlib
pull requests), and for `Coarse/Geometry/Group/WordMetricBounds.lean` (milestone M3).
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

attribute [blueprint "Group.Generators.dist_le_mul_wordLength" (latexEnv := "lemma")
  (title := /-- Lipschitz principle -/)
  (statement := /-- Let $\varphi \colon G \to X$ satisfy $d(\varphi(g), \varphi(g P_i)) \le K$ for
    all $g \in G$ and all $i$. Then $d(\varphi(g), \varphi(h)) \le K\,|g^{-1} h|_P$ for all
    $g, h$. -/)
  (proof := /-- Write $g^{-1} h$ as a geodesic word and apply the triangle inequality along its
    prefixes. -/)
  (proofUses := ["Group.Generators.wordLength"])]
  Group.Generators.dist_le_mul_wordLength

attribute [blueprint "Group.Generators.wordLength_le_mul_wordLength" (latexEnv := "lemma")
  (title := /-- Change of generators, from the proof of L\"oh Prop.~5.2.5 -/)
  (statement := /-- Let $Q$ be another generating family and $M$ a bound for the $Q$-lengths of the
    generators: $|P_i|_Q \le M$ for all $i$ (for finite $P$, $M = \max_i |P_i|_Q$). Then $|g|_Q \le
    M\,|g|_P$. -/)
  (proof := /-- Lemma~\ref{Group.Generators.dist_le_mul_wordLength} for the identity map $(G, d_P)
    \to (G, d_Q)$. This is L\"oh's argument: write $g$ as a product of $|g|_P$ generators and
    inverses, and bound each factor's $Q$-length by $M$. -/)
  (proofUses := ["Group.Generators.dist_le_mul_wordLength", "Group.Generators.groupNorm"])]
  Group.Generators.wordLength_le_mul_wordLength

attribute [blueprint "Group.Generators.finite_setOf_wordLength_le" (latexEnv := "lemma")
  (title := /-- Finite balls -/)
  (statement := /-- If $\iota$ is finite, then $\{g \mid |g|_P \le n\}$ is finite for every $n$. -/)
  (proof := /-- It is the image of the finite set of words of length at most $n$. -/)
  (proofUses := ["Group.Generators.wordLength"])]
  Group.Generators.finite_setOf_wordLength_le
