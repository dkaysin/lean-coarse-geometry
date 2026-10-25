/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Topology.MetricSpace.QuasiIsometry

/-!
# Blueprint: quasi-isometries

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

attribute [blueprint
  "Metric.IsQuasiIsometricEmbedding.of_coarseLipschitzWith_of_coarseAntilipschitzWith"
  (latexEnv := "lemma")
  (statement := /-- A map that is coarse Lipschitz and coarse antilipschitz, with possibly
    different constants, is a $(c, b)$-quasi-isometric embedding for some $c, b$. -/)]
  Metric.IsQuasiIsometricEmbedding.of_coarseLipschitzWith_of_coarseAntilipschitzWith

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
