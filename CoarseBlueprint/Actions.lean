/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Topology.Bornology.MetricallyProperSMul

/-!
# Blueprint: hypotheses on the action

Blueprint nodes for `Coarse/Topology/Bornology/MetricallyProperSMul.lean` (milestone M4).
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
  (proof := /-- A bounded set lies in a closed ball, which is compact; apply the finiteness in the
    definition of a properly discontinuous action. -/)
  (proofUses := ["IsMetricallyProperSMul"])]
  isMetricallyProperSMul_of_properlyDiscontinuousSMul

attribute [blueprint "isMetricallyProperSMul_of_finite" (latexEnv := "lemma")
  (statement := /-- Every action of a finite group is metrically proper, and the restriction of a
    metrically proper action to a subgroup is metrically proper. -/)
  (proof := /-- Subsets of finite sets are finite. -/)
  (proofUses := ["IsMetricallyProperSMul"])]
  isMetricallyProperSMul_of_finite IsMetricallyProperSMul.subgroup

attribute [blueprint "IsCoboundedSMul.of_finiteIndex" (latexEnv := "lemma")
  (statement := /-- If $G$ acts isometrically and coboundedly and $H \le G$ has finite index, then
    $H$ acts coboundedly. -/)
  (proof := /-- If $s$ works for $G$ and $g_1, \dots, g_k$ are coset representatives of $G / H$ (on
    the appropriate side), then $\bigcup_j g_j s$ is bounded and works for $H$. -/)
  (proofUses := ["IsCoboundedSMul"])]
  IsCoboundedSMul.of_finiteIndex
