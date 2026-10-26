/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

import Architect
import Coarse.Geometry.Group.WordMetricBounds

/-!
# Blueprint: coarsely geodesic spaces

Blueprint nodes for `Coarse/Topology/MetricSpace/CoarselyGeodesic.lean` and the word-metric
instance in `Coarse/Geometry/Group/WordMetricBounds.lean` (milestone M2).
-/

attribute [blueprint "Metric.ripsGraph"
  (title := /-- Rips graph -/)
  (statement := /-- The \emph{Rips graph} of a pseudometric space $X$ at scale $r$ is the simple
    graph on $X$ in which distinct points $x, y$ are adjacent if $d(x, y) \le r$ (Cornulier--de la
    Harpe, Def.~3.B.5). Its walks are the $r$-chains, and the length of a walk is its number of
    steps. -/)]
  Metric.ripsGraph

attribute [blueprint "Metric.IsCoarselyConnectedWith"
  (title := /-- Coarsely connected space -/)
  (statement := /-- A pseudometric space $X$ is \emph{$r$-coarsely connected} if it is nonempty and
    any two points are joined by an $r$-chain, i.e.\ its Rips graph at scale $r$ is connected. -/)]
  Metric.IsCoarselyConnectedWith

attribute [blueprint "Metric.IsCoarselyGeodesicWith"
  (title := /-- Coarsely geodesic space -/)
  (statement := /-- A pseudometric space $X$ is \emph{$(r, L, C)$-coarsely geodesic} if any two
    points $x, y$ are joined by an $r$-chain with at most $L\,d(x, y) + C$ steps (Cornulier--de la
    Harpe, Def.~3.B.1 (c), ``large-scale geodesic''). -/)]
  Metric.IsCoarselyGeodesicWith

attribute [blueprint "Metric.IsCoarselyConnected"
  (title := /-- Coarsely connected space, without constants -/)
  (statement := /-- $X$ is \emph{coarsely connected} if it is $r$-coarsely connected for some
    $r$. -/)]
  Metric.IsCoarselyConnected

attribute [blueprint "Metric.IsCoarselyGeodesic"
  (title := /-- Coarsely geodesic space, without constants -/)
  (statement := /-- $X$ is \emph{coarsely geodesic} if it is $(r, L, C)$-coarsely geodesic for some
    $r, L, C$. -/)]
  Metric.IsCoarselyGeodesic

attribute [blueprint "SimpleGraph.Walk.dist_le_mul_length" (latexEnv := "lemma")
  (title := /-- Maps along walks -/)
  (statement := /-- If a map $\varphi$ from the vertices of a graph to a pseudometric space moves
    adjacent vertices by at most $K$, then $d(\varphi(u), \varphi(v)) \le K n$ for every walk of
    length $n$ from $u$ to $v$. -/)
  (proof := /-- Induction on the walk, with the triangle inequality at each step. -/)]
  SimpleGraph.Walk.dist_le_mul_length

attribute [blueprint "Metric.exists_ripsGraph_walk_length_le" (latexEnv := "lemma")
  (title := /-- Chains from sequences -/)
  (statement := /-- If $x_0, x_1, \dots$ is a sequence of points with $d(x_k, x_{k+1}) \le r$ for
    $k < n$, then there is an $r$-chain from $x_0$ to $x_n$ with at most $n$ steps. -/)
  (proof := /-- Induction on $n$: append $x_{n+1}$ to the chain, unless it equals $x_n$ (the Rips
    graph has no loops), in which case the chain is kept. -/)]
  Metric.exists_ripsGraph_walk_length_le

attribute [blueprint "Metric.IsCoarselyGeodesicWith.coarseLipschitzWith" (latexEnv := "lemma")
  (title := /-- Bounded steps, cf.\ Dru\c{t}u--Kapovich, Lem.~8.8 -/)
  (statement := /-- On an $(r, L, C)$-coarsely geodesic space, a map that moves points at distance
    at most $r$ by at most $A$ is $(A L, A C)$-coarse Lipschitz. -/)
  (proof := /-- Join $x$ to $y$ by an $r$-chain with $n \le L\,d(x, y) + C$ steps. Each step moves
    by at most $A$, so $d(f x, f y) \le A n \le A L\,d(x, y) + A C$ by
    Lemma~\ref{SimpleGraph.Walk.dist_le_mul_length}. Dru\c{t}u--Kapovich prove it
    for geodesic spaces, cutting a geodesic into steps of length $r$. -/)]
  Metric.IsCoarselyGeodesicWith.coarseLipschitzWith

attribute [blueprint "NormedSpace.isCoarselyGeodesicWith" (latexEnv := "lemma")
  (statement := /-- A real normed space is $(r, 1/r, 1)$-coarsely geodesic for every $r > 0$. -/)
  (proof := /-- Take the points $x + \frac{k}{m}(y - x)$ for $k = 0, \dots, m$ and $m = \max(\lceil
    \|x - y\| / r \rceil, 1)$: consecutive points are at distance $\|x - y\| / m \le r$, and
    $m \le \|x - y\| / r + 1$. Lemma~\ref{Metric.exists_ripsGraph_walk_length_le} turns them into
    an $r$-chain with at most $m$ steps. -/)]
  NormedSpace.isCoarselyGeodesicWith

attribute [blueprint "Group.Generators.isCoarselyGeodesicWith" (latexEnv := "lemma")
  (statement := /-- A group with the word metric of a generating family, $(G, d_P)$, is
    $(1, 1, 0)$-coarsely geodesic. -/)
  (proof := /-- Adjacent vertices of the Cayley graph differ by a generator or its inverse, so they
    are at distance at most $1$: the Cayley graph maps into the Rips graph of $(G, d_P)$ at scale
    $1$. A geodesic word for $g^{-1} h$ gives a walk in the Cayley graph from $g$ to $h$ with at
    most $|g^{-1} h|_P = d(g, h)$ steps. -/)]
  Group.Generators.isCoarselyGeodesicWith
