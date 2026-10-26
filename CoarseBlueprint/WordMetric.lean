/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

import Architect
import Coarse.Geometry.Group.CayleySimpleGraph
import Coarse.Geometry.Group.WithWordMetric
import Coarse.Geometry.Group.WordMetric
import Coarse.Geometry.Group.WordMetricBounds

/-!
# Blueprint: word metrics

Blueprint nodes for `Coarse/GroupTheory/Generators.lean` and
`Coarse/Geometry/Group/{WordMetric, CayleySimpleGraph}.lean` (milestone M3; copies of open Mathlib
pull requests), and for `Coarse/Geometry/Group/{WithWordMetric, WordMetricBounds}.lean`
(milestone M3).
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

attribute [blueprint "Group.Generators.WithWordMetric"
  (title := /-- Group with a word metric -/)
  (statement := /-- $(G, d_P)$ is a copy of $G$ carrying the word metric of $P$. The copies for
    different generating families are different spaces, and the identity of $G$ is the map
    $\mathrm{congr}_{P,Q} \colon (G, d_P) \to (G, d_Q)$. -/)]
  Group.Generators.WithWordMetric Group.Generators.WithWordMetric.congr

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
  (title := /-- cf.\ Bridson--Haefliger, Lem.~I.8.18 -/)
  (statement := /-- Let $\varphi \colon G \to X$ satisfy $d(\varphi(g), \varphi(g P_i)) \le K$ for
    all $g \in G$ and all $i$. Then $d(\varphi(g), \varphi(h)) \le K\,|g^{-1} h|_P$ for all
    $g, h$: $\varphi$ is $K$-Lipschitz for the word metric of $P$. -/)
  (proof := /-- Adjacent vertices of the Cayley graph differ by right multiplication by a
    generator, in one direction or the other, so $\varphi$ moves them by at most $K$. By
    Lemma~\ref{SimpleGraph.Walk.dist_le_mul_length}, $\varphi$ then moves the endpoints of a walk
    by at most $K$ times its length. A geodesic word for $g^{-1} h$ gives a walk from $g$ to $h$ of
    length at most $|g^{-1} h|_P$. -/)]
  Group.Generators.dist_le_mul_wordLength

attribute [blueprint "Group.Generators.wordLength_le_mul_wordLength" (latexEnv := "lemma")
  (title := /-- Change of generators, from the proof of L\"oh Prop.~5.2.5 -/)
  (statement := /-- Let $Q$ be another generating family and $K$ a bound for the $Q$-lengths of the
    generators: $|P_i|_Q \le K$ for all $i$ (for finite $P$, $K = \max_i |P_i|_Q$). Then $|g|_Q \le
    K\,|g|_P$. -/)
  (proof := /-- Lemma~\ref{Group.Generators.dist_le_mul_wordLength} for the identity map
    $G \to (G, d_Q)$, which moves $g$ and $g P_i$ apart by $d_Q(g, g P_i) = |P_i|_Q \le K$, at
    $1$ and $g$. This is L\"oh's argument: write $g$ as a product of $|g|_P$ generators and
    inverses, and bound each factor's $Q$-length by $K$. -/)]
  Group.Generators.wordLength_le_mul_wordLength

attribute [blueprint "Group.Generators.finite_setOf_wordLength_le" (latexEnv := "lemma")
  (title := /-- Finite balls -/)
  (statement := /-- If $\iota$ is finite, then $\{g \mid |g|_P \le n\}$ is finite for every $n$. -/)
  (proof := /-- It is the image of the finite set of words of length at most $n$. -/)]
  Group.Generators.finite_setOf_wordLength_le
