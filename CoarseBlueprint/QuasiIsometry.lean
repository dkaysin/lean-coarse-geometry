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

attribute [blueprint "LipschitzWith.coarseLipschitzWith" (latexEnv := "lemma")
  (statement := /-- An $L$-Lipschitz map is $(L, 0)$-coarse Lipschitz. -/)]
  LipschitzWith.coarseLipschitzWith

attribute [blueprint "Metric.CoarseLipschitzWith.mono" (latexEnv := "lemma")
  (statement := /-- An $(L, C)$-coarse Lipschitz map is $(L', C')$-coarse Lipschitz for
    $L \le L'$ and $C \le C'$. -/)]
  Metric.CoarseLipschitzWith.mono

attribute [blueprint "Metric.CoarseLipschitzWith.comp" (latexEnv := "lemma")
  (statement := /-- If $f$ is $(L_1, C_1)$- and $g$ is $(L_2, C_2)$-coarse Lipschitz, then
    $g \circ f$ is $(L_2 L_1, L_2 C_1 + C_2)$-coarse Lipschitz. -/)]
  Metric.CoarseLipschitzWith.comp

attribute [blueprint "Metric.CoarseAntilipschitzWith"
  (title := /-- Coarse antilipschitz map -/)
  (statement := /-- A map $f \colon X \to Y$ is \emph{$(L, C)$-coarse antilipschitz} if
    $d(x, y) \le L\,d(f x, f y) + C$ for all $x, y$. -/)]
  Metric.CoarseAntilipschitzWith

attribute [blueprint "AntilipschitzWith.coarseAntilipschitzWith" (latexEnv := "lemma")
  (statement := /-- An $L$-antilipschitz map is $(L, 0)$-coarse antilipschitz. -/)]
  AntilipschitzWith.coarseAntilipschitzWith

attribute [blueprint "Metric.coarseAntilipschitzWith_iff_inv_mul_sub_le" (latexEnv := "lemma")
  (statement := /-- For $L \ne 0$, $f$ is $(L, L C)$-coarse antilipschitz if and only if
    $L^{-1} d(x, y) - C \le d(f x, f y)$ for all $x, y$. -/)]
  Metric.coarseAntilipschitzWith_iff_inv_mul_sub_le

attribute [blueprint "Metric.CoarseAntilipschitzWith.mono" (latexEnv := "lemma")
  (statement := /-- An $(L, C)$-coarse antilipschitz map is $(L', C')$-coarse antilipschitz for
    $L \le L'$ and $C \le C'$. -/)]
  Metric.CoarseAntilipschitzWith.mono

attribute [blueprint "Metric.CoarseAntilipschitzWith.comp" (latexEnv := "lemma")
  (statement := /-- If $f$ is $(L_1, C_1)$- and $g$ is $(L_2, C_2)$-coarse antilipschitz, then
    $g \circ f$ is $(L_1 L_2, L_1 C_2 + C_1)$-coarse antilipschitz. -/)]
  Metric.CoarseAntilipschitzWith.comp

attribute [blueprint "Metric.HasFiniteDist"
  (title := /-- Maps at finite distance -/)
  (statement := /-- Maps $f, g \colon W \to Y$ have \emph{finite distance} if there is $c$ with
    $d(f x, g x) \le c$ for all $x$ (L\"oh, Def.~5.1.6). -/)]
  Metric.HasFiniteDist

attribute [blueprint "Metric.HasFiniteDist.refl" (latexEnv := "lemma")
  (statement := /-- Every map has finite distance from itself. -/)]
  Metric.HasFiniteDist.refl Metric.HasFiniteDist.rfl

attribute [blueprint "Metric.HasFiniteDist.symm" (latexEnv := "lemma")
  (statement := /-- Having finite distance is symmetric. -/)]
  Metric.HasFiniteDist.symm

attribute [blueprint "Metric.HasFiniteDist.trans" (latexEnv := "lemma")
  (statement := /-- Having finite distance is transitive. -/)]
  Metric.HasFiniteDist.trans

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

attribute [blueprint "Metric.quasiDenseRange_iff_exists_isCover" (latexEnv := "lemma")
  (statement := /-- A map has quasi-dense range if and only if its range is a $c$-cover of the
    codomain for some $c$. -/)]
  Metric.quasiDenseRange_iff_exists_isCover

attribute [blueprint "Metric.IsQuasiIsometricEmbedding.of_hasFiniteDist_comp_id"
  (latexEnv := "lemma")
  (statement := /-- If $f$ is a quasi-isometric embedding and $f \circ g$ has finite distance
    from the identity, then $g$ is a quasi-isometric embedding. -/)
  (proof := /-- As in the proof of L\"oh, Prop.~5.1.10: if $f \circ g$ has distance $D$ from the
    identity, then $d(f g y, f g y')$ and $d(y, y')$ differ by at most $2D$; apply the two bounds
    of $f$ to $g y$ and $g y'$. -/)]
  Metric.IsQuasiIsometricEmbedding.of_hasFiniteDist_comp_id

attribute [blueprint "Metric.IsQuasiIsometricEmbedding.hasFiniteDist_comp_id" (latexEnv := "lemma")
  (statement := /-- If $f$ is a quasi-isometric embedding and $f \circ g$ has finite distance
    from the identity, then so does $g \circ f$. -/)
  (proof := /-- As in the proof of L\"oh, Prop.~5.1.10: if $f$ is a $(c, b)$-quasi-isometric
    embedding and $f \circ g$ has distance $D$ from the identity, the lower bound of $f$ gives
    $d(g f x, x) \le c\,d(f g f x, f x) + c b \le c D + c b$. -/)]
  Metric.IsQuasiIsometricEmbedding.hasFiniteDist_comp_id

attribute [blueprint "Metric.isQuasiIsometry_iff_quasiDenseRange"
  (title := /-- L\"oh, Prop.~5.1.10 -/)
  (statement := /-- A map is a quasi-isometry if and only if it is a quasi-isometric embedding
    with quasi-dense range. -/)
  (proof := /-- As in L\"oh. If $g$ is a quasi-inverse, $f \circ g$ has finite distance from the
    identity, so $f$ has quasi-dense range. Conversely, choose $g(y)$ with $d(f g y, y) \le c$.
    Then $f \circ g$ has finite distance from the identity, so $g$ is a quasi-isometric embedding
    (Lemma~\ref{Metric.IsQuasiIsometricEmbedding.of_hasFiniteDist_comp_id}) and $g \circ f$ has
    finite distance from the identity
    (Lemma~\ref{Metric.IsQuasiIsometricEmbedding.hasFiniteDist_comp_id}). -/)]
  Metric.isQuasiIsometry_iff_quasiDenseRange
