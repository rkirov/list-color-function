/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Choosable
import Monophilic.ThetaChoosable
import Monophilic.Theta

/-!
# Rubin's theorem: the easy direction, and what remains

**Rubin's characterization.** Due to A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor,
*Choosability in graphs*, Proc. West Coast Conf. on Combinatorics, Graph Theory and Computing
(Arcata, California, 1979), Congr. Numer. **26**, Utilitas Math., Winnipeg, **1980**, 125–157:

> a connected graph is `2`-choosable **iff** its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

Kirov–Naimi's Theorem 2 cites this. **It is not proved in this development.** The goal is to prove
it, so that Theorem 2 carries no hypothesis; until then `Monophilic.RubinTheorem` in
`Monophilic.Theorem2` names the statement and is the first explicit argument of
`Monophilic.monophilic_two_iff_of_rubin`, so that supplying a term of that type — and nothing else —
discharges Theorem 2.

What **is** proved, here, is the **⟸ direction**: every graph on Rubin's list really is
`2`-choosable. The outstanding half is ⟹.

## What is proved here

The three families, each already established in the files this one imports:

* a single vertex — `SimpleGraph.choosable_of_subsingleton`;
* an even cycle — `Monophilic.choosable_two_closePath_of_odd`, which is a corollary of **Theorem 1**:
  `2`-monophilicity says the constant assignment minimizes, and that minimum is `col(C,2) = 2 > 0`;
* `θ_{2,2,2m}` — `Monophilic.choosable_theta`.

Passing from the core back to the whole graph is `SimpleGraph.choosable_pendantTower_iff`. Together
these give `choosable_two_of_rubinFamily` below.

## What remains, and a correction

Only the **⟹ direction** — that a `2`-choosable graph *must* have one of those three cores.

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
generalized theta, **or** contains two cycles meeting in at most one vertex* — is **false**.
`K₃,₃` minus an edge refutes it on six vertices: four of its vertices have degree `≥ 3` whereas a
generalized theta has exactly two, and its girth is `4`, so two cycles meeting in at most one vertex
would need seven. An exhaustive sweep of the 129,073 bipartite 2-connected non-cycle graphs on
`≤ 9` vertices finds 4,162 satisfying neither branch. The alternative that closes all 129,073 cases adds a third branch — *is* a generalized theta,
**or** contains a dumbbell, **or** contains a `θ(a,b,c)` of shape other than `(2,2,\text{even})` —
but that is an **empirical observation, not a theorem**, and `plan.md` records what would be needed
to establish it.

Given a correct structural statement, the rest is in place: an odd cycle is not `2`-colourable
(hence not `2`-choosable), choosability passes to subgraphs (`SimpleGraph.Choosable.mono`,
`SimpleGraph.Choosable.comap`), a **dumbbell** is not `2`-choosable
(`Monophilic.not_choosable_two_of_dumbbell` — note the connecting path is load-bearing, since two
*disjoint* even cycles are `2`-choosable), and `θ(a,b,c)` is `2`-choosable exactly for shape
`(2,2,\text{even})` (`Monophilic.choosable_two_thetaGen_iff`, **proved**). What is missing is the
extraction, and Mathlib has no vertex connectivity, blocks or ear decomposition to build it on.

## Main results

* `Monophilic.choosable_two_of_rubinFamily` — Rubin's ⟸ direction, proved

`SimpleGraph.monophilic_two_iff_of_rubin_hard` and `monophilic_two_iff_of_rubin'` below state
Theorem 2 with its three core alternatives left as abstract propositions. They are **superseded** by
`Monophilic.monophilic_two_iff_of_rubin` in `Monophilic.Theorem2`, which uses concrete `CoreIs`
notions and takes Rubin's theorem as a single named hypothesis to be discharged. They are kept only
until that discharge lands.
-/

namespace Monophilic

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
than a separate argument. `2`-monophilicity says the constant list assignment *minimizes* the number
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

end Monophilic

namespace SimpleGraph

/-- **Theorem 2 of Kirov–Naimi, borrowing only the hard direction of Rubin's theorem.**

This strengthens `SimpleGraph.monophilic_two_iff_of_rubin`, which assumed Rubin as an `↔`. Only the
forward implication was ever used, and the backward one — that the three families really are
`2`-choosable — is now proved in `Monophilic.choosable_two_of_rubinFamily`. So the hypothesis here
is a one-way implication, and the borrowed statement is correspondingly smaller.

As before the three alternatives are kept as abstract propositions, so that nothing about cores can
be smuggled in and the loan stays legible in the signature. -/
theorem monophilic_two_iff_of_rubin_hard {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 →
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.Monophilic 2)
    (hcycle : CoreIsEvenCycle → G.Monophilic 2)
    (hK23 : CoreIsTheta 1 → G.Monophilic 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.Monophilic 2) :
    G.Monophilic 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 := by
  constructor
  · intro hmono
    by_cases hcol : G.Colorable 2
    · rcases rubin (choosable_of_monophilic_of_colorable hmono hcol) with h | h | ⟨m, hm, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · have hm1 : m = 1 := by omega
          exact Or.inr (Or.inr (Or.inr (hm1 ▸ h)))
        · exact absurd hmono (htheta m hm2 h)
    · exact Or.inl hcol
  · rintro (h | h | h | h)
    · exact monophilic_of_not_colorable h
    · exact hvertex h
    · exact hcycle h
    · exact hK23 h

/-- The previous, weaker form is now a corollary: an `↔` hypothesis certainly supplies the forward
implication. -/
theorem monophilic_two_iff_of_rubin' {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 ↔
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.Monophilic 2)
    (hcycle : CoreIsEvenCycle → G.Monophilic 2)
    (hK23 : CoreIsTheta 1 → G.Monophilic 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.Monophilic 2) :
    G.Monophilic 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 :=
  monophilic_two_iff_of_rubin_hard rubin.mp hvertex hcycle hK23 htheta

end SimpleGraph
