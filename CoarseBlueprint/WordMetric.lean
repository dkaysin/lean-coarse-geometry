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

attribute [blueprint "def:generators"
  (title := /-- Generating family -/)
  (statement := /-- A \emph{generating family} of a group $G$ indexed by $\iota$ is a map
    $\iota \to G$ whose range generates $G$. -/)]
  Group.Generators

attribute [blueprint "lem:fg-of-finite-generators" (latexEnv := "lemma")
  (statement := /-- A group with a finite generating family is finitely generated, and a
    finitely generated group has a finite generating family. -/)]
  Group.Generators.fg Group.fg_iff_nonempty_finite_generators

attribute [blueprint "def:word-length"
  (title := /-- Word length -/)
  (statement := /-- The \emph{word length} $|g|_P$ of $g$ is the least length of a word in the
    generators and their inverses whose product is $g$. -/)]
  Group.Generators.wordLength

attribute [blueprint "lem:word-length-wordprod-le" (latexEnv := "lemma")
  (statement := /-- The word length of the product of a word is at most the length of the
    word. -/)]
  Group.Generators.wordLength_wordProd_le

attribute [blueprint "lem:word-length-le-iff" (latexEnv := "lemma")
  (statement := /-- $|g|_P \le n$ if and only if $g$ is the product of a word of length at most
    $n$. -/)]
  Group.Generators.wordLength_le_iff

attribute [blueprint "lem:word-length-eq-zero-iff" (latexEnv := "lemma")
  (statement := /-- $|g|_P = 0$ if and only if $g = 1$. -/)]
  Group.Generators.wordLength_eq_zero_iff

attribute [blueprint "lem:word-length-inv" (latexEnv := "lemma")
  (statement := /-- $|g^{-1}|_P = |g|_P$. -/)]
  Group.Generators.wordLength_inv

attribute [blueprint "lem:word-length-mul-le" (latexEnv := "lemma")
  (statement := /-- $|g h|_P \le |g|_P + |h|_P$. -/)]
  Group.Generators.wordLength_mul_le

attribute [blueprint "def:word-metric"
  (title := /-- Word metric -/)
  (statement := /-- The word length is a group norm; the \emph{word metric} is
    $d_P(g, h) = |g^{-1} h|_P$ (L\"oh, Def.~5.2.3). -/)]
  Group.Generators.groupNorm Group.Generators.normedGroup

attribute [blueprint "def:cayley-graph"
  (title := /-- Cayley graph -/)
  (statement := /-- The \emph{Cayley graph} of $P$ has vertex set $G$, with $g$ and $h$
    adjacent when $g \ne h$ and $g^{-1} h$ is a generator or the inverse of one. -/)]
  Group.Generators.cayleySimpleGraph

attribute [blueprint "thm:dist-cayley-graph"
  (statement := /-- The graph distance in the Cayley graph is the word metric:
    $d(g, h) = |g^{-1} h|_P$. -/)]
  Group.Generators.dist_cayleySimpleGraph
