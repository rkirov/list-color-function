/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Choosable
import ListColoring.ThetaChoosable
import ListColoring.Theta

/-!
# Rubin's theorem: the easy direction, and what remains

**Rubin's characterization.** Due to A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor,
*Choosability in graphs*, Proc. West Coast Conf. on Combinatorics, Graph Theory and Computing
(Arcata, California, 1979), Congr. Numer. **26**, Utilitas Math., Winnipeg, **1980**, 125–157:

> a connected graph is `2`-choosable **iff** its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

Kirov–Naimi's Theorem 2 cites this. **It is now proved in this development**, as
`ListColoring.rubinTheorem` in `ListColoring.RubinProof`; `ListColoring.RubinTheorem` in
`ListColoring.Theorem2` names the statement and is the first explicit argument of
`ListColoring.ecc_two_iff_of_rubin`, so supplying that term — and nothing else — discharges
Theorem 2, which it does in `ListColoring.ecc_two_iff`.

What is proved **here** is only the **⟸ direction**: every graph on Rubin's list really is
`2`-choosable. The ⟹ direction is the long one, and lives downstream, in
`ListColoring.RubinStructure`, `ListColoring.RubinCases` and `ListColoring.CoreExtract`, assembled
in `ListColoring.RubinProof`.

## What is proved here

The three families, each already established in the files this one imports:

* a single vertex — `SimpleGraph.choosable_of_subsingleton`;
* an even cycle — `ListColoring.choosable_two_closePath_of_odd`, which is a corollary of **Theorem
  1**: enumerative chromatic-choosability at `2` says the constant assignment minimizes, and that
  minimum is `col(C,2) = 2 > 0`;
* `θ_{2,2,2m}` — `ListColoring.choosable_theta`.

Passing from the core back to the whole graph is `SimpleGraph.choosable_pendantTower_iff`. Together
these give `choosable_two_of_rubinFamily` below.

## The other direction, and a correction on the way to it

The **⟹ direction** — that a `2`-choosable graph *must* have one of those three cores — is proved,
but not by the route this section describes. The record below is kept because the refutations in it
are the only durable content of the detour.

An earlier version of this file claimed the remaining work reduced to the structural fact that *a
connected graph of minimum degree `≥ 2` that is not a cycle contains a theta subgraph*. **That is
false**, and the mis-statement was this repository's, not the literature's. `K₂,₄` is connected, has
minimum degree `2` and is not a cycle, yet every theta subgraph of it is the *good* `θ_{2,2,2}`; it
is nonetheless not `2`-choosable. The error was reading "theta" as the three-path graph. The
structural object is the **generalized** theta `Θ(k₁,…,k_n)` — `n` internally disjoint paths between
two vertices, `n` arbitrary — and `K₂,₄` is the one with four paths of length `2`.

**That correction was itself insufficient**, and the details matter, because *contains* and *is*
behave completely differently here.

*Containing* a generalized theta is the wrong predicate — nearly vacuous. `K₃,₃ − e` contains both
`θ(1,3,3)` and `θ(2,2,2)`; `K₂,₄` contains only `θ(2,2,2)`. Since the good `θ(2,2,2m)` **is**
`2`-choosable, exhibiting a theta subgraph implies nothing whatever. What matters is containing a
**bad** one.

The natural repair in its *is* form — *connected, minimum degree `≥ 2`, not a cycle ⟹ **is** a
generalized theta, **or** contains two cycles meeting in at most one vertex* — is **false**. `K₃,₃`
minus an edge refutes it on six vertices: four of its vertices have degree `≥ 3` whereas a
generalized theta has exactly two, and its girth is `4`, so two cycles meeting in at most one vertex
would need seven. An exhaustive sweep of the 129,073 bipartite 2-connected non-cycle graphs on `≤ 9`
vertices finds 4,162 satisfying neither branch. The alternative that closes all 129,073 cases adds a
third branch — *is* a generalized theta, **or** contains a dumbbell, **or** contains a `θ(a,b,c)` of
shape other than `(2,2,\text{even})` — but that is an **empirical observation, not a theorem**, and
`plan.md` records what would be needed to establish it.

**No such structural statement is used in the end.** The ⟹ direction is proved instead by Rubin's
own argument, which never needs one: take a *shortest* cycle `C₁` and, if any edge lies off it, a
shortest path `P₁` edge-disjoint from `C₁` joining two of its vertices; minimality forces `C₁` to be
a four-cycle and `P₁` to have even length, and a further case analysis shows no edge can lie outside
`C₁ ∪ P₁`. That is `ListColoring.RubinStructure` and `ListColoring.RubinCases`, ending in
`ListColoring.rubin_structure`, with the passage to and from the core in `ListColoring.CoreExtract`
and the assembly in `ListColoring.RubinProof`.

The pieces listed above are what that argument runs on: an odd cycle is not `2`-colourable (hence
not `2`-choosable), choosability passes to subgraphs (`SimpleGraph.Choosable.mono`,
`SimpleGraph.Choosable.comap`), a **dumbbell** is not `2`-choosable
(`ListColoring.not_choosable_two_of_dumbbell` — note the connecting path is load-bearing, since two
*disjoint* even cycles are `2`-choosable), and `θ(a,b,c)` is `2`-choosable exactly for shape
`(2,2,\text{even})` (`ListColoring.choosable_two_thetaGen_iff`, **proved**). Mathlib has no vertex
connectivity, blocks or ear decomposition, and none is needed.

## Main results

* `ListColoring.choosable_two_of_rubinFamily` — Rubin's ⟸ direction, proved

`SimpleGraph.ecc_two_iff_of_rubin_hard` and `ecc_two_iff_of_rubin'` below state
Theorem 2 with its three core alternatives left as abstract propositions. They are **superseded** by
`ListColoring.ecc_two_iff` in `ListColoring.RubinProof`, which uses concrete `CoreIs` notions and
assumes nothing beyond connectivity, Rubin's theorem having been discharged by
`ListColoring.rubinTheorem`. They are kept as a record of the shape of the loan that was outstanding
while the proof was being built.
-/

namespace ListColoring

open SimpleGraph

/-- A graph is on **Rubin's list** when it is a single vertex, an even cycle, or `θ_{2,2,2m}`.
Stated up to isomorphism, since the three families are built on their own vertex types.

`closePath k` has `k + 1` vertices, so `Odd k` picks out the cycles on an *even* number of them. -/
def RubinFamily {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Subsingleton V ∨
  (∃ k, Odd k ∧ 2 ≤ k ∧ Nonempty (G ≃g closePath k)) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (G ≃g theta m))

/-- **Rubin's theorem, ⟸ direction: every graph on Rubin's list is `2`-choosable.**

The even-cycle case is the interesting one: it is a corollary of Theorem 1 of Kirov–Naimi rather
than a separate argument. Enumerative chromatic-choosability at `2` says the constant list
assignment *minimizes* the number
of colourings, and for an even cycle that minimum is `col(C, 2) = 2`; so every `2`-list assignment
admits at least two colourings, in particular at least one. -/
theorem choosable_two_of_rubinFamily {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : RubinFamily G) : G.Choosable 2 := by
  rcases h with hsub | ⟨k, hk, hk2, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact choosable_of_subsingleton (by omega)
  · exact (choosable_iso e 2).mpr (choosable_two_closePath_of_odd hk hk2)
  · exact (choosable_iso e 2).mpr (choosable_theta m hm)

/-- The cycles *excluded* from Rubin's list are excluded for the right reason: a cycle on an odd
number of vertices is not even `2`-colourable. -/
theorem not_choosable_two_of_odd_cycle {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    ¬ (closePath k).Choosable 2 :=
  not_choosable_two_closePath_of_even hk hk2

end ListColoring

namespace SimpleGraph

/-- **Theorem 2 of Kirov–Naimi, borrowing only the hard direction of Rubin's theorem.**

This strengthens `SimpleGraph.ecc_two_iff_of_rubin`, which assumed Rubin as an `↔`. Only the
forward implication was ever used, and the backward one — that the three families really are
`2`-choosable — is now proved in `ListColoring.choosable_two_of_rubinFamily`. So the hypothesis here
is a one-way implication, and the borrowed statement is correspondingly smaller.

As before the three alternatives are kept as abstract propositions, so that nothing about cores can
be smuggled in and the loan stays legible in the signature. -/
theorem ecc_two_iff_of_rubin_hard {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 →
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.ECCAt 2)
    (hcycle : CoreIsEvenCycle → G.ECCAt 2)
    (hK23 : CoreIsTheta 1 → G.ECCAt 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.ECCAt 2) :
    G.ECCAt 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 := by
  constructor
  · intro hmono
    by_cases hcol : G.Colorable 2
    · rcases rubin (choosable_of_ecc_of_colorable hmono hcol) with h | h | ⟨m, hm, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · have hm1 : m = 1 := by omega
          exact Or.inr (Or.inr (Or.inr (hm1 ▸ h)))
        · exact absurd hmono (htheta m hm2 h)
    · exact Or.inl hcol
  · rintro (h | h | h | h)
    · exact ecc_of_not_colorable h
    · exact hvertex h
    · exact hcycle h
    · exact hK23 h

/-- The previous, weaker form is now a corollary: an `↔` hypothesis certainly supplies the forward
implication. -/
theorem ecc_two_iff_of_rubin' {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 ↔
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.ECCAt 2)
    (hcycle : CoreIsEvenCycle → G.ECCAt 2)
    (hK23 : CoreIsTheta 1 → G.ECCAt 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.ECCAt 2) :
    G.ECCAt 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 :=
  ecc_two_iff_of_rubin_hard rubin.mp hvertex hcycle hK23 htheta

end SimpleGraph
