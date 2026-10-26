/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

import Architect
import Coarse.Geometry.Group.CayleySimpleGraph
import Coarse.Geometry.Group.Hyperbolic
import Coarse.Geometry.Group.HyperbolicGenerators
import Coarse.Geometry.Group.SvarcMilnor
import Coarse.Geometry.Group.WithWordMetric
import Coarse.Geometry.Group.WordMetric
import Coarse.Geometry.Group.WordMetricBounds
import Coarse.Topology.Bornology.MetricallyProperSMul
import Coarse.Topology.CoarseSpace.CoarseEquiv.Defs
import Coarse.Topology.CoarseSpace.Metric.SvarcMilnor
import Coarse.Topology.MetricSpace.QuasiGeodesic
import Coarse.Topology.MetricSpace.QuasiIsometry
import Coarse.Topology.MetricSpace.SlimTriangles

/-!
# Blueprint tags

The blueprint nodes of all chapters, one section per chapter, in the order of
`blueprint/src/content.tex`.

## Implementation notes

All tags are in one module because LeanArchitect extracts each module in an environment made of
that module and its imports, and writes `\uses` only for nodes tagged there; tags spread over
several modules lose the edges between them.
-/

/-! ## Quasi-isometries

Blueprint nodes for `Coarse/Topology/MetricSpace/{CoarseLipschitz, CoarseAntilipschitz,
FiniteDistance, QuasiIsometry}.lean` (milestone M1).
-/

attribute [blueprint "Metric.CoarseLipschitzWith"
  (title := /-- Coarse Lipschitz map -/)
  (statement := /-- A map $f \colon X \to Y$ is \emph{$(L, C)$-coarse Lipschitz} if
    $d(f x, f y) \le L\,d(x, y) + C$ for all $x, y$ (Dru\c{t}u--Kapovich, Def.~8.5). -/)]
  Metric.CoarseLipschitzWith

attribute [blueprint "Metric.CoarseAntilipschitzWith"
  (title := /-- Coarse antilipschitz map -/)
  (statement := /-- A map $f \colon X \to Y$ is \emph{$(L, C)$-coarse antilipschitz} if
    $d(x, y) \le L\,d(f x, f y) + C$ for all $x, y$. -/)]
  Metric.CoarseAntilipschitzWith

attribute [blueprint "Metric.HasFiniteDist"
  (title := /-- Maps at finite distance -/)
  (statement := /-- Maps $f, g \colon W \to Y$ have \emph{finite distance} if there is $c$ with
    $d(f x, g x) \le c$ for all $x$ (L\"oh, Def.~5.1.6). -/)]
  Metric.HasFiniteDist

attribute [blueprint "Metric.IsQuasiIsometricEmbeddingWith"
  (title := /-- Quasi-isometric embedding with constants -/)
  (statement := /-- A map $f$ is a \emph{$(c, b)$-quasi-isometric embedding} if it is
    $(c, b)$-coarse Lipschitz and $(c, c b)$-coarse antilipschitz; for $c > 0$ this says
    $c^{-1} d(x, y) - b \le d(f x, f y) \le c\,d(x, y) + b$, as in L\"oh, Def.~5.1.6, where
    $c, b > 0$. -/)]
  Metric.IsQuasiIsometricEmbeddingWith

attribute [blueprint "Metric.IsQuasiIsometricEmbedding"
  (title := /-- Quasi-isometric embedding -/)
  (statement := /-- A map is a \emph{quasi-isometric embedding} if it is a
    $(c, b)$-quasi-isometric embedding for some $c, b$. -/)]
  Metric.IsQuasiIsometricEmbedding

attribute [blueprint "Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding"
  (latexEnv := "lemma")
  (statement := /-- A map that is coarse Lipschitz and coarse antilipschitz, with possibly
    different constants, is a quasi-isometric embedding: if it is $(L_1, C_1)$-coarse Lipschitz
    and $(L_2, C_2)$-coarse antilipschitz, it is a $(\max\{L_1, L_2, 1\}, \max\{C_1,
    C_2\})$-quasi-isometric embedding. -/)
  (proof := /-- Increase the constants of both bounds to $c = \max\{L_1, L_2, 1\}$ and $b =
    \max\{C_1, C_2\}$; the additive constant $C_2$ of the lower bound is at most $c b$ since $c \ge
    1$. -/)]
  Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding
  Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbeddingWith

attribute [blueprint "Metric.IsQuasiIsometry"
  (title := /-- Quasi-isometry -/)
  (statement := /-- A \emph{quasi-isometry} is a quasi-isometric embedding $f$ with a
    quasi-inverse: a quasi-isometric embedding $g$ in the other direction such that $g \circ f$
    and $f \circ g$ have finite distance from the identity (L\"oh, Def.~5.1.6). -/)]
  Metric.IsQuasiIsometry

attribute [blueprint "Metric.QuasiIsometric"
  (title := /-- Quasi-isometric spaces -/)
  (statement := /-- Two spaces are \emph{quasi-isometric} if there is a quasi-isometry between
    them (L\"oh, Def.~5.1.6). -/)]
  Metric.QuasiIsometric

attribute [blueprint "Metric.QuasiDenseRange"
  (title := /-- Quasi-dense range -/)
  (statement := /-- A map $f \colon W \to Y$ has \emph{quasi-dense range} if there is $c$ such
    that every $y \in Y$ satisfies $d(f x, y) \le c$ for some $x$ (L\"oh, Prop.~5.1.10). -/)]
  Metric.QuasiDenseRange

attribute [blueprint "Metric.isQuasiIsometry_iff_quasiDenseRange"
  (title := /-- L\"oh, Prop.~5.1.10 -/)
  (statement := /-- A map is a quasi-isometry if and only if it is a quasi-isometric embedding
    with quasi-dense range. -/)
  (proof := /-- As in L\"oh. If $g$ is a quasi-inverse, $f \circ g$ has finite distance from the
    identity, so $f$ has quasi-dense range. Conversely, choose $g(y)$ with $d(f g y, y) \le c$.
    Then $f \circ g$ has some distance $D$ from the identity. So $d(f g y, f g y')$ and $d(y, y')$
    differ by at most $2D$, and the two bounds of $f$, applied to $g y$ and $g y'$, make $g$ a
    quasi-isometric embedding. If $f$ is a $(c, b)$-quasi-isometric embedding, its lower bound
    gives $d(g f x, x) \le c\,d(f g f x, f x) + c b \le c D + c b$, so $g \circ f$ has finite
    distance from the identity. -/)]
  Metric.isQuasiIsometry_iff_quasiDenseRange

attribute [blueprint "Metric.isQuasiIsometry_of_bilipschitz" (latexEnv := "lemma")
  (title := /-- Bilipschitz maps -/)
  (statement := /-- A surjective map that is Lipschitz and antilipschitz (for possibly different
    constants) is a quasi-isometry. -/)
  (proof := /-- The two bounds are coarse bounds with additive constant $0$, so the map is a
    quasi-isometric embedding by
    Lemma~\ref{Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding}; it is surjective, so its
    range is quasi-dense, and Theorem~\ref{Metric.isQuasiIsometry_iff_quasiDenseRange}
    concludes. -/)]
  Metric.isQuasiIsometry_of_bilipschitz

attribute [blueprint "Metric.CoarseLipschitzWith.isQuasiIsometry" (latexEnv := "lemma")
  (title := /-- Coarse Lipschitz quasi-inverse, cf.\ Dru\c{t}u--Kapovich, Def.~8.10 -/)
  (statement := /-- If $f \colon X \to Y$ and $g \colon Y \to X$ are coarse Lipschitz and $g \circ
    f$ and $f \circ g$ have finite distance from the identity, then $f$ is a quasi-isometry. -/)
  (proof := /-- If $g$ is $(L, C)$-coarse Lipschitz and $d(g f x, x) \le D$, then $d(x, y) \le d(g f
    x, g f y) + 2D \le L\,d(f x, f y) + C + 2D$, so $f$ is coarse antilipschitz, hence a
    quasi-isometric embedding by
    Lemma~\ref{Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding}. Since $f \circ g$ has
    finite distance from the identity, $f$ has quasi-dense range, and
    Theorem~\ref{Metric.isQuasiIsometry_iff_quasiDenseRange} concludes. Dru\c{t}u--Kapovich take
    this as the definition of a quasi-isometry. -/)]
  Metric.CoarseLipschitzWith.isQuasiIsometry

attribute [blueprint "Metric.IsQuasiIsometry.comp" (latexEnv := "lemma")
  (title := /-- L\"oh, Prop.~5.1.11 (5) -/)
  (statement := /-- The composition of two quasi-isometries is a quasi-isometry. -/)
  (proof := /-- Let $f \colon X \to Y$ and $g \colon Y \to Z$ have quasi-inverses $f'$ and $g'$. The
    composite $g \circ f$ is a quasi-isometric embedding (L\"oh, Prop.~5.1.11 (4)): if $f$ is $(L_1,
    C_1)$- and $g$ is $(L_2, C_2)$-coarse Lipschitz, then $g \circ f$ is $(L_2 L_1, L_2 C_1 +
    C_2)$-coarse Lipschitz, the antilipschitz bounds compose in the same way, and
    Lemma~\ref{Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding}
    merges the constants. The same argument makes $f' \circ g'$ a quasi-isometric embedding, and it
    is a quasi-inverse of $g \circ f$. Finite distance is preserved by precomposition with any map
    (with the same constant) and by postcomposition with an $(L, C)$-coarse Lipschitz map (distance
    $D$ becomes $L D + C$; L\"oh, Prop.~5.1.11 (3)). So $f' g' g f$ is at finite distance from $f'
    f$, hence, by the triangle inequality, from the identity; and symmetrically for $g f f' g'$.
    -/)]
  Metric.IsQuasiIsometry.comp

attribute [blueprint "Metric.QuasiIsometric.refl"
  (title := /-- cf.\ L\"oh, Rem.~5.1.12 -/)
  (statement := /-- Being quasi-isometric is an equivalence relation on pseudometric spaces. -/)
  (proof := /-- Reflexivity: the identity is $1$-Lipschitz and $1$-antilipschitz, hence a
    $(1, 0)$-quasi-isometric embedding, and it is its own quasi-inverse, with both composites
    equal to the identity (a special case of L\"oh, Ex.~5.1.7). Symmetry is immediate from the
    definition (the quasi-inverse is a quasi-isometry). Transitivity is
    Lemma~\ref{Metric.IsQuasiIsometry.comp}. L\"oh does not state the theorem; it follows from
    her Remark 5.1.12, where quasi-isometries are the isomorphisms of the category of metric spaces
    and quasi-isometric embeddings up to finite distance. -/)]
  Metric.QuasiIsometric.refl Metric.QuasiIsometric.symm Metric.QuasiIsometric.trans

/-! ## Word metrics

Blueprint nodes for `Coarse/GroupTheory/Generators.lean` and
`Coarse/Geometry/Group/{WordMetric, CayleySimpleGraph}.lean` (milestone M2; copies of open Mathlib
pull requests), and for `Coarse/Geometry/Group/{WithWordMetric, WordMetricBounds}.lean`
(milestone M2).
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

/-! ## Coarsely geodesic spaces and quasi-geodesics

Blueprint nodes for `Coarse/Topology/MetricSpace/{CoarselyGeodesic, QuasiGeodesic}.lean` and the
word-metric instance in `Coarse/Geometry/Group/WordMetricBounds.lean` (milestone M3).
-/

attribute [blueprint "Metric.ripsGraph"
  (title := /-- Rips graph -/)
  (statement := /-- The \emph{Rips graph} of a pseudometric space $X$ at scale $r$ is the simple
    graph on $X$ in which distinct points $x, y$ are adjacent if $d(x, y) \le r$ (Cornulier--de la
    Harpe, Def.~3.B.5). Its walks are the $r$-chains, and the length of a walk is its number of
    steps. -/)]
  Metric.ripsGraph

attribute [blueprint "Metric.IsCoarselyConnectedSpaceWith"
  (title := /-- Coarsely connected space -/)
  (statement := /-- A pseudometric space $X$ is \emph{$r$-coarsely connected} if it is nonempty and
    any two points are joined by an $r$-chain, i.e.\ its Rips graph at scale $r$ is connected. -/)]
  Metric.IsCoarselyConnectedSpaceWith

attribute [blueprint "Metric.IsCoarseGeodesicWith"
  (title := /-- Coarse geodesic -/)
  (statement := /-- An $r$-chain from $x$ to $x'$ is an \emph{$(L, C)$-coarse geodesic} if it has
    at most $L\,d(x, x') + C$ steps. Unlike a geodesic or a quasi-geodesic, a part of a coarse
    geodesic need not be one: only the total number of steps is bounded. -/)]
  Metric.IsCoarseGeodesicWith

attribute [blueprint "Metric.IsCoarselyGeodesicSpaceWith"
  (title := /-- Coarsely geodesic space -/)
  (statement := /-- A pseudometric space $X$ is \emph{$(r, L, C)$-coarsely geodesic} if any two
    points are joined by an $r$-chain that is an $(L, C)$-coarse geodesic (Cornulier--de la Harpe,
    Def.~3.B.1 (c), ``large-scale geodesic''). -/)]
  Metric.IsCoarselyGeodesicSpaceWith

attribute [blueprint "Metric.IsCoarselyConnectedSpace"
  (title := /-- Coarsely connected space, without constants -/)
  (statement := /-- $X$ is \emph{coarsely connected} if it is $r$-coarsely connected for some
    $r$. -/)]
  Metric.IsCoarselyConnectedSpace

attribute [blueprint "Metric.IsCoarselyGeodesicSpace"
  (title := /-- Coarsely geodesic space, without constants -/)
  (statement := /-- $X$ is \emph{coarsely geodesic} if it is $(r, L, C)$-coarsely geodesic for some
    $r, L, C$. -/)]
  Metric.IsCoarselyGeodesicSpace

attribute [blueprint "SimpleGraph.Walk.dist_le_mul_length" (latexEnv := "lemma")
  (title := /-- Maps along walks -/)
  (statement := /-- If a map $\varphi$ from the vertices of a graph to a pseudometric space moves
    adjacent vertices by at most $K$, then $d(\varphi(u), \varphi(v)) \le K n$ for every walk of
    length $n$ from $u$ to $v$. More generally, $d(\varphi(x_i), \varphi(x_j)) \le K (j - i)$ for
    the vertices $x_i, x_j$ at positions $i \le j$ of a walk. -/)
  (proof := /-- Induction on the walk, with the triangle inequality at each step. For positions
    $i \le j$, apply this to the subwalk from $x_i$ to $x_j$. -/)]
  SimpleGraph.Walk.dist_le_mul_length
  SimpleGraph.Walk.dist_getVert_le_mul

attribute [blueprint "SimpleGraph.Walk.dist_getVert_of_length_eq_dist" (latexEnv := "lemma")
  (title := /-- Shortest walks -/)
  (statement := /-- Let $x_0, \dots, x_n$ be the vertices of a walk of length $n = d(x_0, x_n)$ in
    a graph. Then $d(x_i, x_j) = j - i$ for $i \le j \le n$. -/)
  (proof := /-- The subwalk from $x_i$ to $x_j$ has length $j - i$, and a subwalk of a shortest
    walk is a shortest walk (Mathlib's \texttt{SimpleGraph.length\_eq\_dist\_of\_subwalk}). -/)]
  SimpleGraph.Walk.dist_getVert_of_length_eq_dist

attribute [blueprint "Metric.exists_ripsGraph_walk_length_le" (latexEnv := "lemma")
  (title := /-- Chains from sequences -/)
  (statement := /-- If $x_0, x_1, \dots$ is a sequence of points with $d(x_k, x_{k+1}) \le r$ for
    $k < n$, then there is an $r$-chain from $x_0$ to $x_n$ with at most $n$ steps. -/)
  (proof := /-- Induction on $n$: append $x_{n+1}$ to the chain, unless it equals $x_n$ (the Rips
    graph has no loops), in which case the chain is kept. -/)]
  Metric.exists_ripsGraph_walk_length_le

attribute [blueprint "Metric.IsGeodesic.isQuasiGeodesicWith" (latexEnv := "lemma")
  (title := /-- Geodesics are quasi-geodesics -/)
  (statement := /-- A geodesic $\gamma \colon [t, t'] \to X$ from $x$ to $x'$ is a
    $(1, 0)$-quasi-geodesic from $x$ to $x'$. -/)
  (proof := /-- An isometric map is $1$-Lipschitz and $1$-antilipschitz. -/)]
  Metric.IsGeodesic.isQuasiGeodesicWith

attribute [blueprint "Metric.IsQuasiGeodesicWith.exists_isCoarseGeodesicWith" (latexEnv := "lemma")
  (title := /-- Coarse geodesics from quasi-geodesics -/)
  (statement := /-- Let $\gamma$ be a $(c, b)$-quasi-geodesic from $x$ to $x'$, and let
    $\delta > 0$ with $c \delta + b \le r$. Then there is an $r$-chain from $x$ to $x'$ that is a
    $(c / \delta, c b / \delta + 1)$-coarse geodesic. -/)
  (proof := /-- Let $\gamma$ be defined on $[t, t']$ and $n = \lceil (t' - t) / \delta \rceil$, so
    that $n < (t' - t) / \delta + 1$. The points $\gamma(\min\{t + k \delta, t'\})$,
    $k = 0, \dots, n$, run from $\gamma(t) = x$ to $\gamma(t') = x'$ with parameters at most
    $\delta$ apart, so by the upper bound of $\gamma$ they are consecutively at distance at most
    $c \delta + b \le r$, and Lemma~\ref{Metric.exists_ripsGraph_walk_length_le} gives an
    $r$-chain with at most $n$ steps. The lower bound of $\gamma$ at $t$ and $t'$ gives
    $t' - t \le c\,d(x, x') + c b$, so $n \le (c / \delta)\,d(x, x') + c b / \delta + 1$. -/)]
  Metric.IsQuasiGeodesicWith.exists_isCoarseGeodesicWith

attribute [blueprint "Metric.IsCoarselyGeodesicSpaceWith.coarseLipschitzWith" (latexEnv := "lemma")
  (title := /-- Bounded steps, cf.\ Dru\c{t}u--Kapovich, Lem.~8.8 -/)
  (statement := /-- On an $(r, L, C)$-coarsely geodesic space, a map that moves points at distance
    at most $r$ by at most $A$ is $(A L, A C)$-coarse Lipschitz. -/)
  (proof := /-- Join $x$ to $y$ by an $r$-chain with $n \le L\,d(x, y) + C$ steps. Each step moves
    by at most $A$, so $d(f x, f y) \le A n \le A L\,d(x, y) + A C$ by
    Lemma~\ref{SimpleGraph.Walk.dist_le_mul_length}. Dru\c{t}u--Kapovich prove it
    for geodesic spaces, cutting a geodesic into steps of length $r$. -/)]
  Metric.IsCoarselyGeodesicSpaceWith.coarseLipschitzWith

attribute [blueprint "NormedSpace.isCoarselyGeodesicSpaceWith" (latexEnv := "lemma")
  (statement := /-- A real normed space is $(r, 1/r, 1)$-coarsely geodesic for every $r > 0$. -/)
  (proof := /-- Take the points $x + \frac{k}{m}(y - x)$ for $k = 0, \dots, m$ and $m = \max(\lceil
    \|x - y\| / r \rceil, 1)$: consecutive points are at distance $\|x - y\| / m \le r$, and
    $m \le \|x - y\| / r + 1$. Lemma~\ref{Metric.exists_ripsGraph_walk_length_le} turns them into
    an $r$-chain with at most $m$ steps. -/)]
  NormedSpace.isCoarselyGeodesicSpaceWith

attribute [blueprint "Metric.IsGeodesicSpace.isCoarselyGeodesicSpaceWith" (latexEnv := "lemma")
  (title := /-- Geodesic spaces are coarsely geodesic -/)
  (statement := /-- A geodesic pseudometric space is $(r, 1/r, 1)$-coarsely geodesic for every
    $r > 0$. -/)
  (proof := /-- A geodesic from $x$ to $x'$ is a $(1, 0)$-quasi-geodesic
    (Lemma~\ref{Metric.IsGeodesic.isQuasiGeodesicWith}), and
    Lemma~\ref{Metric.IsQuasiGeodesicWith.exists_isCoarseGeodesicWith} with $\delta = r$ gives an
    $r$-chain from $x$ to $x'$ that is a $(1/r, 1)$-coarse geodesic. -/)]
  Metric.IsGeodesicSpace.isCoarselyGeodesicSpaceWith

attribute [blueprint "Group.Generators.isCoarselyGeodesicSpaceWith" (latexEnv := "lemma")
  (statement := /-- A group with the word metric of a generating family, $(G, d_P)$, is
    $(1, 1, 0)$-coarsely geodesic. -/)
  (proof := /-- Adjacent vertices of the Cayley graph differ by a generator or its inverse, so they
    are at distance at most $1$: the Cayley graph maps into the Rips graph of $(G, d_P)$ at scale
    $1$. A geodesic word for $g^{-1} h$ gives a walk in the Cayley graph from $g$ to $h$ with at
    most $|g^{-1} h|_P = d(g, h)$ steps. -/)]
  Group.Generators.isCoarselyGeodesicSpaceWith

attribute [blueprint "Metric.IsQuasiGeodesicWith"
  (title := /-- Quasi-geodesic, Bridson--Haefliger Def.~I.8.22, L\"oh Def.~5.3.4 -/)
  (statement := /-- Let $X$ be a pseudometric space, $c, b \ge 0$ and $t \le t'$. A map $\gamma
    \colon [t, t'] \to X$ is a \emph{$(c, b)$-quasi-geodesic} from $x$ to $x'$ if it is a
    $(c, b)$-quasi-isometric embedding
    (Definition~\ref{Metric.IsQuasiIsometricEmbeddingWith}) with $\gamma(t) = x$ and
    $\gamma(t') = x'$. It need not be continuous. In Lean, $\gamma$ is a map $\R \to X$ satisfying
    the two bounds for parameters in $[t, t']$. -/)]
  Metric.IsQuasiGeodesicWith

attribute [blueprint "Metric.IsQuasiGeodesicSpaceWith"
  (title := /-- Quasi-geodesic space, L\"oh Def.~5.3.4 -/)
  (statement := /-- A pseudometric space $X$ is a \emph{$(c, b)$-quasi-geodesic space} if any two
    of its points are joined by a $(c, b)$-quasi-geodesic. -/)]
  Metric.IsQuasiGeodesicSpaceWith

attribute [blueprint "Metric.IsQuasiGeodesicSpace"
  (title := /-- Quasi-geodesic space, without constants -/)
  (statement := /-- $X$ is a \emph{quasi-geodesic space} if it is a $(c, b)$-quasi-geodesic space
    for some $c, b$. -/)]
  Metric.IsQuasiGeodesicSpace

attribute [blueprint "Metric.isQuasiIsometricEmbeddingWith_intFloor" (latexEnv := "lemma")
  (title := /-- The floor -/)
  (statement := /-- The floor $s \mapsto \lfloor s \rfloor$ from $\R$ to $\Z$ is a
    $(1, 1)$-quasi-isometric embedding. -/)
  (proof := /-- $\lfloor s \rfloor - \lfloor s' \rfloor$ and $s - s'$ differ by less than $1$, so
    their absolute values do too. -/)]
  Metric.isQuasiIsometricEmbeddingWith_intFloor

attribute [blueprint "Metric.isCoarselyGeodesicSpace_iff_isQuasiGeodesicSpace"
  (title := /-- Coarsely geodesic and quasi-geodesic spaces -/)
  (statement := /-- A pseudometric space is coarsely geodesic if and only if it is a quasi-geodesic
    space. More precisely:
    \begin{itemize}
      \item a $(c, b)$-quasi-geodesic space is $(c + b, c, c b + 1)$-coarsely geodesic;
      \item an $(r, L, C)$-coarsely geodesic space is a
            $(\max\{r, L, 1\}, \max\{r, C + 1\})$-quasi-geodesic space.
    \end{itemize} -/)
  (proof := /-- \emph{Quasi-geodesics give chains.} A $(c, b)$-quasi-geodesic from $x$ to $x'$
    gives a $(c + b)$-chain from $x$ to $x'$ that is a $(c, c b + 1)$-coarse geodesic, by
    Lemma~\ref{Metric.IsQuasiGeodesicWith.exists_isCoarseGeodesicWith} with $\delta = 1$.

    \emph{Chains give quasi-geodesics.} Let $d_r$ be the distance of the Rips graph at scale $r$.
    Take a walk $x = x_0, \dots, x_n = x'$ in it of length $n = d_r(x, x')$; it is shortest, so for
    $i, j \le n$, $|i - j| = d_r(x_i, x_j)$
    (Lemma~\ref{SimpleGraph.Walk.dist_getVert_of_length_eq_dist}). Hence
    $d(x_i, x_j) \le r\,|i - j|$ by Lemma~\ref{SimpleGraph.Walk.dist_le_mul_length}, and
    $|i - j| \le L\,d(x_i, x_j) + C$ by the hypothesis. Let $\gamma(s) = x_{\lfloor s \rfloor}$ on
    $[0, n]$, a step function. For $s, s' \in [0, n]$, $|\lfloor s \rfloor - \lfloor s' \rfloor|$
    and $|s - s'|$ differ by at most $1$
    (Lemma~\ref{Metric.isQuasiIsometricEmbeddingWith_intFloor}). So on $[0, n]$,
    $d(\gamma s, \gamma s') \le r\,|s - s'| + r$ and
    $|s - s'| \le L\,d(\gamma s, \gamma s') + C + 1$, which with $c = \max\{r, L, 1\}$ and
    $b = \max\{r, C + 1\}$ are the two bounds of a $(c, b)$-quasi-geodesic ($c \ge 1$ gives
    $C + 1 \le c b$).

    The equivalence follows from the two parts. -/)]
  Metric.isCoarselyGeodesicSpace_iff_isQuasiGeodesicSpace
  Metric.IsQuasiGeodesicSpaceWith.isCoarselyGeodesicSpaceWith
  Metric.IsCoarselyGeodesicSpaceWith.isQuasiGeodesicSpaceWith

/-! ## The Švarc–Milnor lemma

Blueprint nodes for milestone M4: the hypotheses on the action, the lemma and its corollaries.
-/

/-! ### Hypotheses on the action

Nodes in `Coarse/Topology/Bornology/MetricallyProperSMul.lean`, and the action of a group on
itself with a word metric in `Coarse/Geometry/Group/{WithWordMetric,WordMetricBounds}.lean`.
-/

attribute [blueprint "IsMetricallyProperSMul"
  (title := /-- Metrically proper action -/)
  (statement := /-- An action of $G$ on a space $X$ with a bornology is \emph{metrically proper}
    if for every bounded set $B \subseteq X$ the set $\{g \in G \mid g B \cap B \ne \emptyset\}$
    is finite. -/)]
  IsMetricallyProperSMul

attribute [blueprint "IsCoboundedSMul"
  (title := /-- Cobounded action -/)
  (statement := /-- The action is \emph{cobounded} if some bounded set $s \subseteq X$ satisfies
    $\bigcup_{g \in G} g s = X$. -/)]
  IsCoboundedSMul

attribute [blueprint "isMetricallyProperSMul_of_properlyDiscontinuousSMul" (latexEnv := "lemma")
  (statement := /-- A properly discontinuous action on a proper metric space is metrically
    proper. -/)
  (proof := /-- A bounded set lies in its closure, which is compact since the space is proper;
    apply the finiteness in the definition of a properly discontinuous action. -/)]
  isMetricallyProperSMul_of_properlyDiscontinuousSMul

attribute [blueprint "isMetricallyProperSMul_of_finite" (latexEnv := "lemma")
  (statement := /-- Every action of a finite group is metrically proper, and the restriction of a
    metrically proper action to a subgroup is metrically proper. -/)
  (proof := /-- Subsets of finite sets are finite. -/)]
  isMetricallyProperSMul_of_finite IsMetricallyProperSMul.subgroup

attribute [blueprint "IsCoboundedSMul.of_finiteIndex" (latexEnv := "lemma")
  (statement := /-- If $G$ acts isometrically and coboundedly and $H \le G$ has finite index, then
    $H$ acts coboundedly. -/)
  (proof := /-- If $s$ works for $G$ and $g_1, \dots, g_k$ represent the left cosets $g_j H$,
    then $\bigcup_j g_j^{-1} s$ is bounded, since the action is isometric, and works for $H$: for
    $x \in g s$, write $g^{-1} = g_j h$ with $h \in H$; then $h^{-1} x \in g_j^{-1} s$. -/)]
  IsCoboundedSMul.of_finiteIndex

attribute [blueprint "isCoboundedSMul_of_compactSpace_quotient" (latexEnv := "lemma")
  (title := /-- Cocompact actions are cobounded -/)
  (statement := /-- If $G$ acts isometrically on a pseudometric space $X$ and the orbit space $X/G$,
    with the quotient topology, is compact, then the action is cobounded. -/)
  (proof := /-- If $X$ is empty, the empty set is bounded and covers $X$. Otherwise fix $x_0 \in X$.
    The distance to the orbit $G x_0$ is a continuous function on $X$, constant on orbits, so it
    induces a continuous function on the compact space $X/G$, which is bounded, say by $\rho$. So
    every point is within $\rho + 1$ of a point $g x_0$, that is, lies in $g\,\bar B(x_0, \rho +
    1)$. (This is \texttt{exists\_smul\_closedBall\_eq\_univ} in the copied coarse-space
    library.) -/)]
  isCoboundedSMul_of_compactSpace_quotient

attribute [blueprint "Group.Generators.WithWordMetric.isMetricallyProperSMul" (latexEnv := "lemma")
  (title := /-- A group acts on itself with a word metric -/)
  (statement := /-- $G$ acts isometrically on $(G, d_P)$ by left multiplication, and coboundedly.
    If $P$ is finite, the action is metrically proper. -/)
  (proof := /-- \emph{Isometric}: $(g x)^{-1} (g y) = x^{-1} y$. \emph{Cobounded}: the translates
    of $\{1\}$ cover $G$. \emph{Metrically proper}: a bounded set $s$ lies in a ball around $1$,
    which is finite by Lemma~\ref{Group.Generators.finite_setOf_wordLength_le}; if $g a = b$ with
    $a, b \in s$, then $g = b a^{-1}$, so $\{g \mid g s \cap s \ne \emptyset\}$ lies in the finite
    set $s s^{-1}$. -/)]
  Group.Generators.WithWordMetric.isMetricallyProperSMul
  Group.Generators.WithWordMetric.instMulAction
  Group.Generators.WithWordMetric.instIsIsometricSMul
  Group.Generators.WithWordMetric.isCoboundedSMul

/-! ### The lemma

Nodes in `Coarse/Geometry/Group/SvarcMilnor.lean`.
-/

attribute [blueprint "Group.fg_of_isCoboundedSMul"
  (title := /-- \v{S}varc--Milnor lemma, finite generation -/)
  (statement := /-- A group acting isometrically, metrically properly and coboundedly on a coarsely
    connected pseudometric space is finitely generated. -/)
  (proof := /-- Let $X$ be $r$-coarsely connected, and choose for each $y \in X$ some $\psi(y) \in
    G$ with $y \in \psi(y) s$.

    \emph{One step.} If $d(y, y') \le r$, then $\psi(y)^{-1} \psi(y') \in S$: the point
    $\psi(y)^{-1} y'$ lies in $\psi(y)^{-1} \psi(y') s \subseteq \psi(y)^{-1} \psi(y') B$, and
    within $r$ of $\psi(y)^{-1} y \in s$, so also in $B$. Similarly, an element $t$ that maps a
    point of $s$ into $s$ lies in $S$.

    \emph{$S$ generates $G$.} Let $H$ be the subgroup generated by $S$. By the first step the coset
    $\psi(y) H$ does not change along an $r$-chain (in Lean, induct on the walk in the Rips graph),
    so $\psi(x_0) H = \psi(g x_0) H$ for every $g$. Both $\psi(x_0)$ and $\psi(g x_0)^{-1} g$ map a
    point of $s$ into $s$ (the points $\psi(x_0)^{-1} x_0$ and $x_0$), so they lie in $S$. Hence $g
    = \psi(x_0) \cdot \psi(x_0)^{-1} \psi(g x_0) \cdot \psi(g x_0)^{-1} g \in H$.

    \emph{$S$ is finite}, since $B$ is bounded and the action is metrically proper. So $S$ is a
    finite generating set, and $G$ is finitely generated.

    \emph{Comparison with the references.} L\"oh (Prop.~5.4.1) and Dru\c{t}u--Kapovich
    (Thm.~8.37) write $g$ as the product of the steps $\psi(y_i)^{-1} \psi(y_{i+1})$ along a chain
    from $x_0$ to $g x_0$. Here the chain only shows that $\psi$ is constant modulo $H$. Like L\"oh,
    and unlike Dru\c{t}u--Kapovich, who take steps shorter than the gap between $B$ and the
    translates $g B$ with $g \notin S$, the proof thickens $B$ by the step size $r$. -/)]
  Group.fg_of_isCoboundedSMul

attribute [blueprint "Group.Generators.isQuasiIsometry_smul_const"
  (title := /-- \v{S}varc--Milnor lemma, quasi-isometry -/)
  (statement := /-- Under the same hypotheses, with $X$ coarsely geodesic, every orbit map $g
    \mapsto g x_0$ is a quasi-isometry from $G$ with the word metric of any finite generating
    family. The bound on the number of steps cannot be dropped: $\Z$ acting by translations on $(\R,
    \sqrt{d})$ satisfies every other hypothesis. -/)
  (proof := /-- Let $X$ be $(r, L, C)$-coarsely geodesic, let $P$ be the generating family and
    $|\cdot|_P$ its word length, and let $\psi$ be as in the proof of
    Theorem~\ref{Group.fg_of_isCoboundedSMul}. $S$ is finite, so its elements have word length at
    most some $K$; let $D = \max_i d(x_0, p_i x_0)$ over the generators $p_i$ of $P$.

    \emph{The orbit map $f(g) = g x_0$ is $D$-Lipschitz} by
    Lemma~\ref{Group.Generators.dist_le_mul_wordLength}: right multiplication by $p_i$ moves $g
    x_0$ by $d(x_0, p_i x_0) \le D$.

    \emph{$\psi$ is coarse Lipschitz} into $(G, d_P)$: by the first step of the proof of
    Theorem~\ref{Group.fg_of_isCoboundedSMul}, $|\psi(y)^{-1} \psi(y')|_P \le K$ when $d(y, y') \le
    r$, so $\psi$ is $(K L, K C)$-coarse Lipschitz by
    Lemma~\ref{Metric.IsCoarselyGeodesicSpaceWith.coarseLipschitzWith}.

    \emph{$\psi$ is a quasi-inverse of $f$.} $\psi(g x_0)^{-1} g \in S$, so $d(\psi(f(g)), g) \le
    K$; and $y$ and $\psi(y) x_0$ both lie in $\psi(y) s$, so $d(f(\psi(y)), y) \le \diam s$.
    Lemma~\ref{Metric.CoarseLipschitzWith.isQuasiIsometry} concludes.

    \emph{Comparison with the references.} L\"oh (Prop.~5.4.1) and Dru\c{t}u--Kapovich
    (Thm.~8.37) prove the lower bound $|g^{-1} h|_S \lesssim d(g x_0, h x_0)$ by writing $g^{-1} h$
    as the product of the steps along a chain, for the word metric $d_S$; a finite family $P$ then
    needs the change of generators (Lemma~\ref{Group.Generators.wordLength_le_mul_wordLength}).
    Here the lower bound is the coarse Lipschitz bound of the quasi-inverse $\psi$, as in
    Dru\c{t}u--Kapovich, Lem.~8.29 (for uniformly proper maps), and $d_P$ is used directly, with no
    change of generators. -/)]
  Group.Generators.isQuasiIsometry_smul_const

attribute [blueprint "Group.fg_of_properlyDiscontinuousSMul" (latexEnv := "corollary")
  (title := /-- \v{S}varc--Milnor lemma, topological form, finite generation, L\"oh Cor.~5.4.2 -/)
  (statement := /-- A group acting isometrically, properly discontinuously and cocompactly on a
    nonempty proper geodesic pseudometric space is finitely generated. -/)
  (proof := /-- The action is metrically proper
    (Lemma~\ref{isMetricallyProperSMul_of_properlyDiscontinuousSMul}) and cobounded
    (Lemma~\ref{isCoboundedSMul_of_compactSpace_quotient}), and the space is coarsely geodesic
    (Lemma~\ref{Metric.IsGeodesicSpace.isCoarselyGeodesicSpaceWith}), hence coarsely connected,
    as it is nonempty. Apply Theorem~\ref{Group.fg_of_isCoboundedSMul}. -/)]
  Group.fg_of_properlyDiscontinuousSMul

attribute [blueprint "Group.Generators.isQuasiIsometry_smul_const_of_properlyDiscontinuousSMul"
  (latexEnv := "corollary")
  (title := /-- \v{S}varc--Milnor lemma, topological form, quasi-isometry, L\"oh Cor.~5.4.2 -/)
  (statement := /-- Under the same hypotheses, every orbit map $g \mapsto g x_0$ is a
    quasi-isometry from $G$ with the word metric of any finite generating family. -/)
  (proof := /-- As for Corollary~\ref{Group.fg_of_properlyDiscontinuousSMul}, with
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_const} in place of
    Theorem~\ref{Group.fg_of_isCoboundedSMul}. -/)]
  Group.Generators.isQuasiIsometry_smul_const_of_properlyDiscontinuousSMul

/-! ### Corollaries

Nodes in `Coarse/Geometry/Group/{WordMetricBounds, SvarcMilnor}.lean`.
-/

attribute [blueprint "Group.Generators.WithWordMetric.exists_lipschitzWith_congr"
  (latexEnv := "lemma")
  (title := /-- Change of generators is Lipschitz -/)
  (statement := /-- For a finite generating family $P$ and any generating family $Q$ of $G$, the
    identity $\mathrm{congr}_{P,Q} \colon (G, d_P) \to (G, d_Q)$ is Lipschitz. -/)
  (proof := /-- The generators of $P$ have $Q$-lengths bounded by some $K$, as there are finitely
    many, and Lemma~\ref{Group.Generators.wordLength_le_mul_wordLength} gives $d_Q \le K d_P$. -/)]
  Group.Generators.WithWordMetric.exists_lipschitzWith_congr

attribute [blueprint "Group.Generators.WithWordMetric.isQuasiIsometry_congr"
  (latexEnv := "corollary")
  (title := /-- Change of generators, L\"oh Prop.~5.2.5 -/)
  (statement := /-- For finite generating families $P$ and $Q$ of $G$, the identity
    $\mathrm{congr}_{P,Q} \colon (G, d_P) \to (G, d_Q)$ is a quasi-isometry (it is even
    bilipschitz). -/)
  (proof := /-- As in L\"oh: by
    Lemma~\ref{Group.Generators.WithWordMetric.exists_lipschitzWith_congr} in both
    directions, $\mathrm{congr}_{P,Q}$ is a bijection that is Lipschitz with a Lipschitz inverse,
    hence antilipschitz, and Lemma~\ref{Metric.isQuasiIsometry_of_bilipschitz} concludes. -/)]
  Group.Generators.WithWordMetric.isQuasiIsometry_congr

attribute [blueprint "Subgroup.isQuasiIsometry_subtype" (latexEnv := "corollary")
  (title := /-- Finite-index subgroups -/)
  (statement := /-- If $G$ is finitely generated and $H \le G$ has finite index, then the inclusion
    $H \to G$ is a quasi-isometry for any finite generating families of $H$ and $G$. -/)
  (proof := /-- $H$ acts on $(G, d_P)$ by left multiplication, isometrically, metrically properly
    (by restriction of the action of $G$,
    Lemma~\ref{Group.Generators.WithWordMetric.isMetricallyProperSMul}) and coboundedly (by finite
    index, Lemma~\ref{IsCoboundedSMul.of_finiteIndex}). Apply
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_const} with $x_0 = 1$, whose orbit map is
    the inclusion. -/)]
  Subgroup.isQuasiIsometry_subtype

attribute [blueprint "QuotientGroup.isQuasiIsometry_mk" (latexEnv := "corollary")
  (title := /-- Quotients by finite normal subgroups, L\"oh Cor.~5.4.7 -/)
  (statement := /-- Let $N$ be a finite normal subgroup of $G$, and $P$, $Q$ finite generating
    families of $G$ and $G/N$. Then the quotient map $(G, d_P) \to (G/N, d_Q)$ is a
    quasi-isometry. -/)
  (proof := /-- $G$ acts on $(G/N, d_Q)$ through the quotient map, $g \cdot x = (gN)x$,
    isometrically (Lemma~\ref{Group.Generators.WithWordMetric.isMetricallyProperSMul}, for $G/N$
    acting on itself). The action is metrically proper: for a bounded $B$, the elements $g$ with $g
    B \cap B \ne \emptyset$ are the preimage under the quotient map of the finite set of $h \in
    G/N$ with $h B \cap B \ne \emptyset$ (by the same lemma), and this preimage is finite since
    the fibres of the quotient map are cosets of the finite group $N$. The action is cobounded, with
    the set $\{1\}$, since the quotient map is surjective. The word metric of $Q$ is coarsely
    geodesic (Lemma~\ref{Group.Generators.isCoarselyGeodesicSpaceWith}). Apply
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_const} with $x_0 = 1$, whose orbit map is
    the quotient map. L\"oh's statement also says that $G/N$ is finitely generated if and only if
    $G$ is; that part is not stated here. -/)]
  QuotientGroup.isQuasiIsometry_mk

attribute [blueprint "Int.quasiIsometric_pi_euclideanSpace" (latexEnv := "corollary")
  (title := /-- $\Z^n$ and $\R^n$, L\"oh Ex.~5.2.8 -/)
  (statement := /-- $\Z^n$ with the word metric of any finite generating family (for instance the
    standard basis) is quasi-isometric to $\R^n$. -/)
  (proof := /-- $\Z^n$ acts on $\R^n$ by translations, isometrically. The action is metrically
    proper: if $v + a = b$ with $a, b$ in a bounded set $B$, then every coordinate of $v$ is at most
    $\|v\| = d(a, b) \le \diam B$ in absolute value, which leaves finitely many $v$. It is
    cobounded: the translates of the unit cube $[0, 1]^n$, which is compact, hence bounded, cover
    $\R^n$, since $x = \lfloor x \rfloor + \{x\}$ coordinatewise. $\R^n$ is coarsely geodesic
    (Lemma~\ref{NormedSpace.isCoarselyGeodesicSpaceWith}).
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_const}, in its form for additive groups,
    makes the orbit map of $0$ a quasi-isometry. L\"oh argues directly instead: the inclusion
    $\Z^n \to \R^n$ is a quasi-isometric embedding with quasi-dense image, hence a quasi-isometry
    (Theorem~\ref{Metric.isQuasiIsometry_iff_quasiDenseRange}). Going through
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_const} tests the main theorem. -/)]
  Int.quasiIsometric_pi_euclideanSpace

/-! ## Coarse spaces

Blueprint nodes for `Coarse/Topology/CoarseSpace/` (milestone M5; a copy of S. Ghobash's
coarse-space library).
-/

attribute [blueprint "CoarseSpace"
  (title := /-- Coarse space -/)
  (statement := /-- A \emph{coarse structure} on $X$ is a family of \emph{controlled} subsets of
    $X \times X$ that contains the diagonal and is closed under subsets, finite unions,
    inverses and composition. It is encoded by the filter of complements of controlled
    sets. -/)]
  CoarseSpace

attribute [blueprint "IsCoarselyClose"
  (title := /-- Coarsely close maps -/)
  (statement := /-- Maps $f, g \colon W \to X$ are \emph{coarsely close} if
    $\{(f w, g w)\}$ is controlled. -/)]
  IsCoarselyClose

attribute [blueprint "IsCoarseMap"
  (title := /-- Coarse map -/)
  (statement := /-- A map is \emph{coarse} if it maps controlled sets to controlled sets and
    preimages of coarsely bounded sets are coarsely bounded. -/)]
  IsCoarseMap

attribute [blueprint "CoarseEquiv"
  (title := /-- Coarse equivalence -/)
  (statement := /-- A \emph{coarse equivalence} is a pair of controlled maps in opposite
    directions whose composites are coarsely close to the identities. -/)]
  CoarseEquiv

attribute [blueprint "PseudoEMetricSpace.toCoarseSpace"
  (title := /-- Metric coarse structure -/)
  (statement := /-- In a pseudo-(e)metric space, a set of pairs is controlled if the distance
    is bounded on it. -/)]
  PseudoEMetricSpace.toCoarseSpace

attribute [blueprint "Metric.isControlled_iff" (latexEnv := "lemma")
  (title := /-- Controlled sets of a pseudometric space -/)
  (statement := /-- In a pseudometric space, a set of pairs is controlled for the metric coarse
    structure if and only if the distance is bounded on it. -/)]
  Metric.isControlled_iff

attribute [blueprint "mulOrbitMetricCoarseEquiv"
  (title := /-- Coarse \v{S}varc--Milnor lemma -/)
  (statement := /-- A group with a proper left-invariant metric, acting isometrically, properly
    discontinuously and cocompactly on a proper metric space, is coarsely equivalent to it via
    an orbit map. -/)]
  mulOrbitMetricCoarseEquiv

/-! ## Uniformly discrete spaces and bounded geometry

Blueprint nodes for milestone M6. None is formalized yet.
-/

/-! ## Definitions of hyperbolicity

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
  (statement := /-- Let $X$ be a pseudometric space. A \emph{geodesic} from $x$ to $x'$ is an
    isometric map $\gamma \colon [t, t'] \to X$, for some $t \le t'$, with $\gamma(t) = x$ and
    $\gamma(t') = x'$ (then $t' - t = d(x, x')$). The space $X$ is \emph{geodesic} if any two points
    are joined by a geodesic. In Lean, $\gamma$ is a map $\R \to X$ of which only the values on
    $[t, t']$ matter. -/)]
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
  (proof := /-- By Theorem~\ref{Group.Generators.isHyperbolic_iff_isQuasiHyperbolic}, $G$ is
    hyperbolic if and only if the word metric of $P$ is quasi-hyperbolic, and by
    Theorem~\ref{Group.Generators.isQuasiHyperbolic_iff} this holds if and only if that word metric
    satisfies the four-point condition with some constant. -/)
  (proofUses := ["Group.Generators.isHyperbolic_iff_isQuasiHyperbolic",
    "Group.Generators.isQuasiHyperbolic_iff"])]
  Group.Generators.isHyperbolic_iff

/-! ## Geometric realisation and stability of quasi-geodesics

Blueprint nodes for milestone M8. None is formalized yet.
-/

/-! ## The Gromov boundary

Blueprint nodes for milestone M9. None is formalized yet.
-/

/-! ## Quasi-isometry invariance of the Gromov boundary

Blueprint nodes for milestone M10. None is formalized yet.
-/
