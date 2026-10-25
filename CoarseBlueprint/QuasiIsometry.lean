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

attribute [blueprint "Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding"
  (latexEnv := "lemma")
  (statement := /-- A map that is coarse Lipschitz and coarse antilipschitz, with possibly
    different constants, is a $(c, b)$-quasi-isometric embedding for some $c, b$. -/)]
  Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding

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
    f$, hence, by the triangle inequality, from the identity; and symmetrically for $g f f' g'$. -/)
  (proofUses := ["Metric.IsQuasiIsometry",
    "Metric.CoarseAntilipschitzWith.isQuasiIsometricEmbedding"])]
  Metric.IsQuasiIsometry.comp

attribute [blueprint "Metric.QuasiIsometric.refl"
  (title := /-- cf.\ L\"oh, Rem.~5.1.12 -/)
  (statement := /-- Being quasi-isometric is an equivalence relation on pseudometric spaces. -/)
  (proof := /-- Reflexivity: the identity, and more generally every isometric bijection, is a
    quasi-isometry (L\"oh, Ex.~5.1.7), since an isometric embedding is a $(1, 0)$-quasi-isometric
    embedding and the inverse is a quasi-inverse with both composites equal to the identity.
    Symmetry is immediate from the definition (the quasi-inverse is a quasi-isometry). Transitivity
    is Lemma~\ref{Metric.IsQuasiIsometry.comp}. L\"oh does not state the theorem; it follows from
    her Remark 5.1.12, where quasi-isometries are the isomorphisms of the category of metric spaces
    and quasi-isometric embeddings up to finite distance. -/)
  (proofUses := ["Metric.QuasiIsometric", "Metric.IsQuasiIsometricEmbeddingWith",
    "Metric.IsQuasiIsometry.comp"])]
  Metric.QuasiIsometric.refl Metric.QuasiIsometric.symm Metric.QuasiIsometric.trans
