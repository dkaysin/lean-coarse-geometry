/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
import Architect
import Coarse.Geometry.Group.SvarcMilnor

/-!
# Blueprint: the Švarc–Milnor lemma

Blueprint nodes for `Coarse/Geometry/Group/SvarcMilnor.lean` (milestone M5).
-/

attribute [blueprint "Group.fg_of_isMetricallyProperSMul_of_isCoboundedSMul"
  (title := /-- \v{S}varc--Milnor lemma, finite generation -/)
  (statement := /-- A group acting isometrically, metrically properly and coboundedly on a nonempty
    coarsely connected pseudometric space is finitely generated. -/)
  (proof := /-- Let $X$ be $r$-coarsely connected. \emph{$S$ generates $G$.} Take an $r$-chain $x_0
    = y_0, \dots, y_n = g x_0$ and pick $h_i$ with $y_i \in h_i s$, with $h_0 = 1$ and $h_n = g$.
    Then $h_i^{-1} y_{i+1}$ lies in $h_i^{-1} h_{i+1} s \subseteq h_i^{-1} h_{i+1} B$, and within
    $r$ of $h_i^{-1} y_i \in s$, so also in $B$: hence $h_i^{-1} h_{i+1} \in S$. So $g = \prod_i
    h_i^{-1} h_{i+1}$ is a product of $n$ elements of $S$. (Choose the $h_i$ with \texttt{choose} on
    the covering hypothesis, then patch the endpoints; write the telescoping product over
    \texttt{List.finRange n}.)

    \emph{$S$ is finite}, since $B$ is bounded and the action is metrically proper.

    A finite generating set gives a generating family indexed by a finite type, so $G$ is finitely
    generated. -/)
  (proofUses := ["Metric.IsCoarselyConnectedWith", "IsCoboundedSMul", "IsMetricallyProperSMul",
    "Group.Generators"])]
  Group.fg_of_isMetricallyProperSMul_of_isCoboundedSMul

attribute [blueprint "Group.Generators.isQuasiIsometry_smul_left"
  (title := /-- \v{S}varc--Milnor lemma, quasi-isometry -/)
  (statement := /-- Under the same hypotheses, with $X$ coarsely geodesic, every orbit map $g
    \mapsto g x_0$ is a quasi-isometry from $G$ with the word metric of any finite generating
    family. The bound on the number of steps cannot be dropped: $\Z$ acting by translations on $(\R,
    \sqrt{d})$ satisfies every other hypothesis. -/)
  (proof := /-- Let $X$ be $(r, L, C)$-coarsely geodesic; it is in particular $r$-coarsely
    connected, so by the proof of
    Theorem~\ref{Group.fg_of_isMetricallyProperSMul_of_isCoboundedSMul} $S$ is a finite generating
    set. Work first with the word length $|\cdot|_S$.

    \emph{Lower bound.} The chain argument above, applied to a chain from $x_0$ to $g^{-1} h x_0$
    with $n \le L\,d(x_0, g^{-1} h x_0) + C$ steps, writes $g^{-1} h$ as a product of $n$ elements
    of $S$; each has word length at most $1$, so $|g^{-1} h|_S \le L\,d(g x_0, h x_0) + C$, using
    $d(g x_0, h x_0) = d(x_0, g^{-1} h x_0)$.

    \emph{Upper bound.} For $t \in S$ pick $b \in B$ with $t b \in B$; as $x_0 \in B$, $d(x_0, t
    x_0) \le d(x_0, t b) + d(t b, t x_0) \le 2 \diam B$. $S$ is closed under inverses, so
    Lemma~\ref{Group.Generators.dist_le_mul_wordLength}, applied to the orbit map, gives $d(g x_0, h
    x_0) \le 2 \diam B\,|g^{-1} h|_S$.

    \emph{Density.} If $y \in g s$, then $g^{-1} y$ and $x_0$ both lie in $s$, so $d(y, g x_0) \le
    \diam s$: the orbit map has quasi-dense range.

    The two bounds make the orbit map a quasi-isometric embedding by
    Lemma~\ref{Metric.IsQuasiIsometricEmbedding.of_coarseLipschitzWith_of_coarseAntilipschitzWith}
    and with the density Theorem~\ref{Metric.isQuasiIsometry_iff_quasiDenseRange} makes it a
    quasi-isometry. For another finite family, compose with the identity of $G$, which is a
    quasi-isometry by Lemma~\ref{Group.Generators.wordLength_le_mul_wordLength}
    (Lemma~\ref{Metric.IsQuasiIsometry.comp}). -/)
  (proofUses := ["Metric.IsCoarselyGeodesicWith", "IsCoboundedSMul", "IsMetricallyProperSMul",
    "Group.Generators.groupNorm", "Group.Generators.dist_le_mul_wordLength",
    "Group.Generators.wordLength_le_mul_wordLength",
    "Metric.IsQuasiIsometricEmbedding.of_coarseLipschitzWith_of_coarseAntilipschitzWith",
    "Metric.QuasiDenseRange", "Metric.isQuasiIsometry_iff_quasiDenseRange",
    "Metric.IsQuasiIsometry.comp"])]
  Group.Generators.isQuasiIsometry_smul_left
