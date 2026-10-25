/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Geometry.Group.SvarcMilnor

/-!
# Blueprint: corollaries

Blueprint nodes for the corollaries in `Coarse/Geometry/Group/{WordMetricBounds,
SvarcMilnor}.lean` (milestone M6).
-/

attribute [blueprint "Group.Generators.isQuasiIsometry_id" (latexEnv := "corollary")
  (title := /-- Change of generators, L\"oh Prop.~5.2.5 -/)
  (statement := /-- For finite generating families $P$ and $Q$ of $G$, the identity $(G, d_P) \to
    (G, d_Q)$ is a quasi-isometry (it is even bilipschitz). -/)
  (proof := /-- Lemma~\ref{Group.Generators.wordLength_le_mul_wordLength} in both directions, as in
    L\"oh. -/)
  (proofUses := ["Group.Generators.wordLength_le_mul_wordLength", "Group.Generators.groupNorm",
    "Metric.IsQuasiIsometry",
    "Metric.IsQuasiIsometricEmbedding.of_coarseLipschitzWith_of_coarseAntilipschitzWith"])]
  Group.Generators.isQuasiIsometry_id

attribute [blueprint "Subgroup.isQuasiIsometry_subtype" (latexEnv := "corollary")
  (title := /-- Finite-index subgroups -/)
  (statement := /-- If $G$ is finitely generated and $H \le G$ has finite index, then the inclusion
    $H \to G$ is a quasi-isometry for any finite generating families of $H$ and $G$. -/)
  (proof := /-- $H$ acts on $(G, d_P)$ by left multiplication; the action is metrically proper by
    finiteness of balls and cobounded by finite index. Apply
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_left} with $x_0 = 1$. -/)
  (proofUses := ["Group.Generators.isQuasiIsometry_smul_left",
    "Group.Generators.isCoarselyGeodesicWith", "Group.Generators.finite_setOf_wordLength_le",
    "isMetricallyProperSMul_of_finite", "IsCoboundedSMul.of_finiteIndex"])]
  Subgroup.isQuasiIsometry_subtype

attribute [blueprint "Int.quasiIsometric_pi_euclideanSpace" (latexEnv := "corollary")
  (title := /-- $\Z^n$ and $\R^n$, L\"oh Ex.~5.2.8 -/)
  (statement := /-- $\Z^n$ with the word metric of any finite generating family (for instance the
    standard basis) is quasi-isometric to $\R^n$. -/)
  (proof := /-- $\Z^n$ acts on $\R^n$ by translations, properly discontinuously and with
    the unit cube as a bounded fundamental set. L\"oh argues directly instead: the inclusion $\Z^n
    \to \R^n$ is a quasi-isometric embedding with quasi-dense image, hence a quasi-isometry
    (Theorem~\ref{Metric.isQuasiIsometry_iff_quasiDenseRange}). Going through
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_left} tests the main theorem. -/)
  (proofUses := ["Group.Generators.isQuasiIsometry_smul_left", "NormedSpace.isCoarselyGeodesicWith",
    "isMetricallyProperSMul_of_properlyDiscontinuousSMul"])]
  Int.quasiIsometric_pi_euclideanSpace
