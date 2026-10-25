/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Geometry.Group.Hyperbolic
import Coarse.Geometry.Group.HyperbolicGenerators
import Coarse.Topology.MetricSpace.SlimTriangles

/-!
# Blueprint: hyperbolic spaces and groups

Blueprint nodes for `Coarse/Topology/MetricSpace/Hyperbolic.lean` and
`Coarse/Geometry/Group/Hyperbolic.lean` (copies of open Mathlib pull requests), and for
`Coarse/Topology/MetricSpace/{Geodesic, SlimTriangles}.lean` and
`Coarse/Geometry/Group/HyperbolicGenerators.lean` (milestone M7).
-/

attribute [blueprint "Metric.IsHyperbolicWith"
  (title := /-- Hyperbolic space -/)
  (statement := /-- A pseudometric space is \emph{$\delta$-hyperbolic} if it satisfies Gromov's
    four-point condition with constant $\delta$, and \emph{hyperbolic} if it is
    $\delta$-hyperbolic for some $\delta$. This is $(\delta)$-hyperbolicity in the sense of
    Bridson--Haefliger, Definition III.H.1.20. -/)]
  Metric.IsHyperbolicWith Metric.IsHyperbolic

attribute [blueprint "Group.Generators.IsHyperbolicWith"
  (title := /-- Hyperbolic group -/)
  (statement := /-- A group is \emph{hyperbolic} if it is hyperbolic for the word metric of some
    finite generating family. -/)]
  Group.Generators.IsHyperbolicWith Group.IsHyperbolic

attribute [blueprint "Metric.IsGeodesic"
  (title := /-- Geodesic space, L\"oh Def.~5.3.1, Bridson--Haefliger Def.~I.1.3 -/)
  (statement := /-- Let $X$ be a pseudometric space. A \emph{geodesic} from $x$ to $y$ is an
    isometric map $\gamma \colon [0, d(x, y)] \to X$ with $\gamma(0) = x$ and $\gamma(d(x, y)) = y$
    (an isometric map from any interval $[0, \ell]$ with these endpoints has $\ell = d(x, y)$). The
    space $X$ is \emph{geodesic} if any two points are joined by a geodesic. -/)]
  Metric.IsGeodesic Metric.IsGeodesicSpace

attribute [blueprint "Metric.HasSlimTrianglesWith"
  (title := /-- Slim triangles, L\"oh Def.~7.2.1, Bridson--Haefliger Def.~III.H.1.1 -/)
  (statement := /-- A \emph{geodesic triangle} with vertices $x, y, z$ in a pseudometric space $X$
    consists of geodesics from $x$ to $y$, from $y$ to $z$ and from $z$ to $x$, its sides. It is
    \emph{$\delta$-slim} if every point of each side is within distance $\delta$ of a point of one
    of the other two sides. The space $X$ has \emph{$\delta$-slim triangles} if every geodesic
    triangle in $X$ is $\delta$-slim. -/)]
  Metric.HasSlimTrianglesWith

attribute [blueprint "Metric.HasSlimTrianglesWith.isHyperbolicWith" (latexEnv := "lemma")
  (title := /-- Slim triangles give the four-point condition, cf.\ Bridson--Haefliger
    Prop.~III.H.1.22 -/)
  (statement := /-- If $X$ has $\delta$-slim triangles and is geodesic, then $X$ satisfies the
    four-point condition with constant $3\delta$. -/)
  (proof := /-- For a geodesic $\sigma$ from $x$ to $y$: (a) $(x \cdot y)_w \le d(w, p)$ for every
    $p$ on $\sigma$, by the triangle inequality; (b) some $p$ on $\sigma$ has $d(w, p) \le (x \cdot
    y)_w + 2\delta$, because by slimness of a triangle $w, x, y$ with side $\sigma$
    (Definition~\ref{Metric.HasSlimTrianglesWith}) and connectedness of $\sigma$ some $p$ is within
    $\delta$ of both other sides. Given $w, x, y, z$, take $p$ as in (b) on a side of a triangle $x,
    y, z$. It is within $\delta$ of a point $q$ on another side, say from $x$ to $z$, and (a) gives
    $(x \cdot z)_w \le d(w, q) \le (x \cdot y)_w + 3\delta$. -/)
  (proofUses := ["Metric.HasSlimTrianglesWith", "Metric.IsHyperbolicWith"])]
  Metric.HasSlimTrianglesWith.isHyperbolicWith

attribute [blueprint "Metric.IsHyperbolicWith.hasSlimTrianglesWith" (latexEnv := "lemma")
  (title := /-- The four-point condition gives slim triangles, cf.\ Bridson--Haefliger
    Prop.~III.H.1.22 -/)
  (statement := /-- If $X$ satisfies the four-point condition with constant $\delta$, then it has
    $3\delta$-slim triangles. -/)
  (proof := /-- Let $p$ lie on the side from $x$ to $y$ of a triangle $x, y, z$. As $(x \cdot y)_p =
    0$, the four-point condition at $p$ gives, say, $(x \cdot z)_p \le \delta$. On the side from $x$
    to $z$, the intermediate value theorem gives $q$ with $(x \cdot q)_p = (q \cdot z)_p$. Their sum
    is $d(p, q) + (x \cdot z)_p$, and the four-point condition at $p$ bounds each by $(x \cdot z)_p
    + \delta$, so $d(p, q) \le (x \cdot z)_p + 2\delta \le 3\delta$. -/)
  (proofUses := ["Metric.HasSlimTrianglesWith", "Metric.IsHyperbolicWith"])]
  Metric.IsHyperbolicWith.hasSlimTrianglesWith

attribute [blueprint "Metric.isHyperbolic_iff_exists_hasSlimTrianglesWith"
  (title := /-- L\"oh Ex.~7.E.10, Bridson--Haefliger Prop.~III.H.1.22 -/)
  (statement := /-- A geodesic pseudometric space is hyperbolic if and only if it has $\delta$-slim
    triangles for some $\delta$. -/)
  (proof := /-- ``If'' is Lemma~\ref{Metric.HasSlimTrianglesWith.isHyperbolicWith}, ``only if'' is
    Lemma~\ref{Metric.IsHyperbolicWith.hasSlimTrianglesWith}. L\"oh leaves the theorem as an
    exercise and suggests going through thin triangles (Exercise 7.E.9); Bridson--Haefliger go
    through the insize. -/)
  (proofUses := ["Metric.HasSlimTrianglesWith.isHyperbolicWith",
    "Metric.IsHyperbolicWith.hasSlimTrianglesWith"])]
  Metric.isHyperbolic_iff_exists_hasSlimTrianglesWith

attribute [blueprint "Group.Generators.isHyperbolic_iff"
  (title := /-- Independence of the generating family -/)
  (statement := /-- For a finite generating family $P$ of $G$, $G$ is hyperbolic if and only if it
    is $\delta$-hyperbolic for the word metric of $P$ for some $\delta$: whether $G$ is hyperbolic
    does not depend on the family. -/)
  (proof := /-- Not planned yet (design decision D18).
    Corollary~\ref{Group.Generators.WithWordMetric.isQuasiIsometry_congr} alone does not suffice:
    the four-point condition is not a quasi-isometry invariant of coarsely geodesic spaces (the
    graph of $|x|$ in $\R^2$ is bilipschitz to $\R$ and not hyperbolic). L\"oh defines hyperbolic
    groups by quasi-hyperbolicity of the Cayley graph (slim quasi-geodesic triangles, Definition
    7.3.1), which is a quasi-isometry invariant directly: quasi-geodesic triangles can be pushed
    forward and pulled back along quasi-isometric embeddings (Proposition 7.2.9). For the four-point
    condition: pass from the word metric to the geometric realisation of the Cayley graph, a
    geodesic space in which it is $\frac12$-dense, with a larger constant; switch to slim triangles
    by Theorem~\ref{Metric.isHyperbolic_iff_exists_hasSlimTrianglesWith}; and carry them along the
    quasi-isometry of Corollary~\ref{Group.Generators.WithWordMetric.isQuasiIsometry_congr}. That
    last step is L\"oh's Corollary 7.2.13 (from Proposition 7.2.9 and Theorem 7.2.10, whose proof
    uses the stability of quasi-geodesics, Theorem 7.2.11), or Bridson--Haefliger Thm.~III.H.1.9
    (from Thm.~III.H.1.7). -/)
  (proofUses := ["Group.Generators.IsHyperbolicWith",
    "Group.Generators.WithWordMetric.isQuasiIsometry_congr",
    "Metric.isHyperbolic_iff_exists_hasSlimTrianglesWith"])]
  Group.Generators.isHyperbolic_iff
