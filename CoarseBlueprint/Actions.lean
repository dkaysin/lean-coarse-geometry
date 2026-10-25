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

attribute [blueprint "def:metrically-proper-smul"
  (title := /-- Metrically proper action -/)
  (statement := /-- An action of $G$ on a space $X$ with a bornology is \emph{metrically proper}
    if for every bounded set $B \subseteq X$ the set $\{g \in G \mid g B \cap B \ne \emptyset\}$
    is finite. -/)]
  IsMetricallyProperSMul
