/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Geometry.Group.Hyperbolic

/-!
# Blueprint: hyperbolic spaces and groups

Blueprint nodes for `Coarse/Topology/MetricSpace/Hyperbolic.lean` and
`Coarse/Geometry/Group/Hyperbolic.lean` (copies of open Mathlib pull requests).
-/

attribute [blueprint "def:hyperbolic-space"
  (title := /-- Hyperbolic space -/)
  (statement := /-- A pseudometric space is \emph{$\delta$-hyperbolic} if it satisfies Gromov's
    four-point condition with constant $\delta$, and \emph{hyperbolic} if it is
    $\delta$-hyperbolic for some $\delta$. -/)]
  Metric.IsHyperbolicWith Metric.IsHyperbolic

attribute [blueprint "def:hyperbolic-group"
  (title := /-- Hyperbolic group -/)
  (statement := /-- A group is \emph{hyperbolic} if it is hyperbolic for the word metric of some
    finite generating family. -/)]
  Group.Generators.IsHyperbolicWith Group.IsHyperbolic
