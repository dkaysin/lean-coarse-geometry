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

attribute [blueprint "Metric.IsCoarselyConnectedWith"
  (title := /-- Coarsely connected space -/)
  (statement := /-- A pseudometric space $X$ is \emph{$r$-coarsely connected} if any two points are
    joined by an $r$-chain. -/)]
  Metric.IsCoarselyConnectedWith

attribute [blueprint "Metric.IsCoarselyGeodesicWith"
  (title := /-- Coarsely geodesic space -/)
  (statement := /-- A pseudometric space $X$ is \emph{$(r, L, C)$-coarsely geodesic} if any two
    points $x, y$ are joined by an $r$-chain with at most $L\,d(x, y) + C$ steps. -/)]
  Metric.IsCoarselyGeodesicWith

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
    a $1$-chain from $g$ to $h$ with $|g^{-1} h|$ steps. -/)
  (proofUses := ["Metric.IsCoarselyGeodesicWith", "Group.Generators.groupNorm"])]
  Group.Generators.isCoarselyGeodesicWith
