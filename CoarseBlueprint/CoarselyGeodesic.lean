/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
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
  (statement := /-- A pseudometric space $X$ is \emph{$r$-coarsely connected} if any two points are
    joined by an $r$-chain, i.e.\ its Rips graph at scale $r$ is preconnected. -/)]
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

attribute [blueprint "NormedSpace.isCoarselyGeodesicWith" (latexEnv := "lemma")
  (statement := /-- A real normed space is $(r, 1/r, 1)$-coarsely geodesic for every $r > 0$. -/)
  (proof := /-- Take the points $x + \frac{k}{n}(y - x)$ for $k = 0, \dots, n$ and $n = \lceil \|y -
    x\| / r \rceil$. -/)
  (proofUses := ["Metric.IsCoarselyGeodesicWith"])]
  NormedSpace.isCoarselyGeodesicWith

attribute [blueprint "Group.Generators.isCoarselyGeodesicWith" (latexEnv := "lemma")
  (statement := /-- A group with the word metric of a generating family is $(1, 1, 0)$-coarsely
    geodesic. -/)
  (proof := /-- The prefixes of a geodesic word for $g^{-1} h$, multiplied on the left by $g$, form
    a $1$-chain from $g$ to $h$ with $|g^{-1} h|$ steps. Equivalently, the Rips graph at scale $1$
    is the Cayley graph, whose distance is the word metric. -/)
  (proofUses := ["Metric.IsCoarselyGeodesicWith", "Group.Generators.groupNorm"])]
  Group.Generators.isCoarselyGeodesicWith
