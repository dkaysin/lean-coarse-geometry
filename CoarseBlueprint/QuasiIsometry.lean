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

attribute [blueprint "def:coarse-lipschitz"
  (title := /-- Coarse Lipschitz map -/)
  (statement := /-- A map $f \colon X \to Y$ is \emph{$(L, C)$-coarse Lipschitz} if
    $d(f x, f y) \le L\,d(x, y) + C$ for all $x, y$ (Dru\c{t}u--Kapovich, Def.~8.5). -/)]
  Metric.CoarseLipschitzWith

attribute [blueprint "lem:lipschitz-coarse-lipschitz" (latexEnv := "lemma")
  (statement := /-- An $L$-Lipschitz map is $(L, 0)$-coarse Lipschitz. -/)]
  LipschitzWith.coarseLipschitzWith

attribute [blueprint "lem:coarse-lipschitz-mono" (latexEnv := "lemma")
  (statement := /-- An $(L, C)$-coarse Lipschitz map is $(L', C')$-coarse Lipschitz for
    $L \le L'$ and $C \le C'$. -/)]
  Metric.CoarseLipschitzWith.mono

attribute [blueprint "lem:coarse-lipschitz-comp" (latexEnv := "lemma")
  (statement := /-- If $f$ is $(L_1, C_1)$- and $g$ is $(L_2, C_2)$-coarse Lipschitz, then
    $g \circ f$ is $(L_2 L_1, L_2 C_1 + C_2)$-coarse Lipschitz. -/)]
  Metric.CoarseLipschitzWith.comp

attribute [blueprint "def:coarse-antilipschitz"
  (title := /-- Coarse antilipschitz map -/)
  (statement := /-- A map $f \colon X \to Y$ is \emph{$(L, C)$-coarse antilipschitz} if
    $d(x, y) \le L\,d(f x, f y) + C$ for all $x, y$. -/)]
  Metric.CoarseAntilipschitzWith

attribute [blueprint "lem:antilipschitz-coarse-antilipschitz" (latexEnv := "lemma")
  (statement := /-- An $L$-antilipschitz map is $(L, 0)$-coarse antilipschitz. -/)]
  AntilipschitzWith.coarseAntilipschitzWith

attribute [blueprint "lem:coarse-antilipschitz-iff" (latexEnv := "lemma")
  (statement := /-- For $L \ne 0$, $f$ is $(L, L C)$-coarse antilipschitz if and only if
    $L^{-1} d(x, y) - C \le d(f x, f y)$ for all $x, y$. -/)]
  Metric.coarseAntilipschitzWith_iff_inv_mul_sub_le

attribute [blueprint "lem:coarse-antilipschitz-mono" (latexEnv := "lemma")
  (statement := /-- An $(L, C)$-coarse antilipschitz map is $(L', C')$-coarse antilipschitz for
    $L \le L'$ and $C \le C'$. -/)]
  Metric.CoarseAntilipschitzWith.mono

attribute [blueprint "lem:coarse-antilipschitz-comp" (latexEnv := "lemma")
  (statement := /-- If $f$ is $(L_1, C_1)$- and $g$ is $(L_2, C_2)$-coarse antilipschitz, then
    $g \circ f$ is $(L_1 L_2, L_1 C_2 + C_1)$-coarse antilipschitz. -/)]
  Metric.CoarseAntilipschitzWith.comp

attribute [blueprint "def:finite-dist"
  (title := /-- Maps at finite distance -/)
  (statement := /-- Maps $f, g \colon W \to Y$ have \emph{finite distance} if there is $c$ with
    $d(f x, g x) \le c$ for all $x$ (L\"oh, Def.~5.1.6). -/)]
  Metric.HasFiniteDist

attribute [blueprint "lem:finite-dist-refl" (latexEnv := "lemma")
  (statement := /-- Every map has finite distance from itself. -/)]
  Metric.HasFiniteDist.refl Metric.HasFiniteDist.rfl

attribute [blueprint "lem:finite-dist-symm" (latexEnv := "lemma")
  (statement := /-- Having finite distance is symmetric. -/)]
  Metric.HasFiniteDist.symm

attribute [blueprint "lem:finite-dist-trans" (latexEnv := "lemma")
  (statement := /-- Having finite distance is transitive. -/)]
  Metric.HasFiniteDist.trans

attribute [blueprint "def:qie-with"
  (title := /-- Quasi-isometric embedding with constants -/)
  (statement := /-- A map $f$ is a \emph{$(c, b)$-quasi-isometric embedding} if it is
    $(c, b)$-coarse Lipschitz and $(c, c b)$-coarse antilipschitz, i.e.
    $c^{-1} d(x, y) - b \le d(f x, f y) \le c\,d(x, y) + b$ (L\"oh, Def.~5.1.6). -/)]
  Metric.IsQuasiIsometricEmbeddingWith

attribute [blueprint "def:qie"
  (title := /-- Quasi-isometric embedding -/)
  (statement := /-- A map is a \emph{quasi-isometric embedding} if it is a
    $(c, b)$-quasi-isometric embedding for some $c, b$. -/)]
  Metric.IsQuasiIsometricEmbedding

attribute [blueprint "lem:qie-of-bounds" (latexEnv := "lemma")
  (statement := /-- A map that is coarse Lipschitz and coarse antilipschitz, with possibly
    different constants, is a $(c, b)$-quasi-isometric embedding for some $c, b$. -/)]
  Metric.IsQuasiIsometricEmbedding.of_coarseLipschitzWith_of_coarseAntilipschitzWith

attribute [blueprint "def:qi"
  (title := /-- Quasi-isometry -/)
  (statement := /-- A \emph{quasi-isometry} is a quasi-isometric embedding $f$ with a
    quasi-inverse: a quasi-isometric embedding $g$ in the other direction such that $g \circ f$
    and $f \circ g$ have finite distance from the identity (L\"oh, Def.~5.1.6). -/)]
  Metric.IsQuasiIsometry

attribute [blueprint "def:quasi-isometric"
  (title := /-- Quasi-isometric spaces -/)
  (statement := /-- Two spaces are \emph{quasi-isometric} if there is a quasi-isometry between
    them (L\"oh, Def.~5.1.6). -/)]
  Metric.QuasiIsometric

attribute [blueprint "def:quasi-dense-range"
  (title := /-- Quasi-dense range -/)
  (statement := /-- A map $f \colon W \to Y$ has \emph{quasi-dense range} if there is $c$ such
    that every $y \in Y$ satisfies $d(f x, y) \le c$ for some $x$ (L\"oh, Prop.~5.1.10). -/)]
  Metric.QuasiDenseRange

attribute [blueprint "lem:quasi-dense-range-iff-cover" (latexEnv := "lemma")
  (statement := /-- A map has quasi-dense range if and only if its range is a $c$-cover of the
    codomain for some $c$. -/)]
  Metric.quasiDenseRange_iff_exists_isCover

attribute [blueprint "lem:qie-quasi-inverse" (latexEnv := "lemma")
  (statement := /-- If $f$ is a quasi-isometric embedding and $f \circ g$ has finite distance
    from the identity, then $g$ is a quasi-isometric embedding. -/)]
  Metric.IsQuasiIsometricEmbedding.of_hasFiniteDist_comp_id

attribute [blueprint "lem:qie-quasi-inverse-comp" (latexEnv := "lemma")
  (statement := /-- If $f$ is a quasi-isometric embedding and $f \circ g$ has finite distance
    from the identity, then so does $g \circ f$. -/)]
  Metric.IsQuasiIsometricEmbedding.hasFiniteDist_comp_id

attribute [blueprint "thm:qi-iff-qie-quasi-dense"
  (title := /-- L\"oh, Prop.~5.1.10 -/)
  (statement := /-- A map is a quasi-isometry if and only if it is a quasi-isometric embedding
    with quasi-dense range. -/)]
  Metric.isQuasiIsometry_iff_quasiDenseRange
