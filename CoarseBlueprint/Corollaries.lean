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
  (proof := /-- $H$ acts on $(G, d_P)$ by left multiplication; the action is metrically proper by
    finiteness of balls and cobounded by finite index. Apply
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_const} with $x_0 = 1$. -/)
  (proofUses := ["Group.Generators.isQuasiIsometry_smul_const",
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
    Theorem~\ref{Group.Generators.isQuasiIsometry_smul_const} tests the main theorem. -/)
  (proofUses := ["Group.Generators.isQuasiIsometry_smul_const",
    "NormedSpace.isCoarselyGeodesicWith", "isMetricallyProperSMul_of_properlyDiscontinuousSMul"])]
  Int.quasiIsometric_pi_euclideanSpace
