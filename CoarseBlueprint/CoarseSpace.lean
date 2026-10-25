/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Topology.CoarseSpace.CoarseEquiv.Defs
import Coarse.Topology.CoarseSpace.Metric.SvarcMilnor

/-!
# Blueprint: coarse spaces

Blueprint nodes for `Coarse/Topology/CoarseSpace/` (a copy of S. Ghobash's coarse-space
library).
-/

attribute [blueprint "def:coarse-space"
  (title := /-- Coarse space -/)
  (statement := /-- A \emph{coarse structure} on $X$ is a family of \emph{controlled} subsets of
    $X \times X$ that contains the diagonal and is closed under subsets, finite unions,
    inverses and composition. It is encoded by the filter of complements of controlled
    sets. -/)]
  CoarseSpace

attribute [blueprint "def:coarsely-close"
  (title := /-- Coarsely close maps -/)
  (statement := /-- Maps $f, g \colon W \to X$ are \emph{coarsely close} if
    $\{(f w, g w)\}$ is controlled. -/)]
  IsCoarselyClose

attribute [blueprint "def:coarse-map"
  (title := /-- Coarse map -/)
  (statement := /-- A map is \emph{coarse} if it maps controlled sets to controlled sets and
    preimages of coarsely bounded sets are coarsely bounded. -/)]
  IsCoarseMap

attribute [blueprint "def:coarse-equiv"
  (title := /-- Coarse equivalence -/)
  (statement := /-- A \emph{coarse equivalence} is a pair of controlled maps in opposite
    directions whose composites are coarsely close to the identities. -/)]
  CoarseEquiv

attribute [blueprint "def:metric-coarse-space"
  (title := /-- Metric coarse structure -/)
  (statement := /-- In a pseudo-(e)metric space, a set of pairs is controlled if the distance
    is bounded on it. -/)]
  PseudoEMetricSpace.toCoarseSpace

attribute [blueprint "lem:coarsely-proper-smul" (latexEnv := "lemma")
  (statement := /-- For a properly discontinuous action on a proper metric space, the orbit map
    of a point is coarsely proper. -/)]
  isCoarselyProperMap_smul_const

attribute [blueprint "thm:coarse-svarc-milnor"
  (title := /-- Coarse \v{S}varc--Milnor lemma -/)
  (statement := /-- A group with a proper left-invariant metric, acting isometrically, properly
    discontinuously and cocompactly on a proper metric space, is coarsely equivalent to it via
    an orbit map. -/)]
  mulOrbitMetricCoarseEquiv
