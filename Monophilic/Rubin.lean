/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Choosable
import Monophilic.ThetaChoosable
import Monophilic.Theta

/-!
# Rubin's theorem: the easy direction, and what remains

Rubin's characterization (Erdős–Rubin–Taylor 1980) says:

> a connected graph is `2`-choosable **iff** its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

Theorem 2 of Kirov–Naimi borrows this. This file proves the **⟸ direction** outright — every graph
on Rubin's list really is `2`-choosable — and isolates precisely what is still borrowed.

## What is proved here

The three families, each already established in the files this one imports:

* a single vertex — `SimpleGraph.choosable_of_subsingleton`;
* an even cycle — `Monophilic.choosable_two_closePath_of_odd`, which is a corollary of **Theorem 1**:
  `2`-monophilicity says the constant assignment minimizes, and that minimum is `col(C,2) = 2 > 0`;
* `θ_{2,2,2m}` — `Monophilic.choosable_theta`.

Passing from the core back to the whole graph is `SimpleGraph.choosable_pendantTower_iff`. Together
these give `choosable_two_of_rubinFamily` below.

## What is still borrowed, and why

Only the **⟹ direction** — that a `2`-choosable graph *must* have one of those three cores. That is
the direction Theorem 2 actually consumes, and `monophilic_two_iff_of_rubin_hard` now takes it as a
one-way implication rather than an `↔`, so the half proved here is no longer assumed.

The remaining direction reduces to a purely *structural* fact with no colouring content in it: a
connected graph of minimum degree `≥ 2` that is not a cycle contains a theta subgraph. Given that,
the rest is: an odd cycle is not `2`-colourable (hence not `2`-choosable), choosability passes to
subgraphs (`SimpleGraph.Choosable.mono`, `SimpleGraph.Choosable.comap`), and a theta whose three
path lengths are not `(2,2,\text{even})` is not `2`-choosable. Mathlib has no block or ear
decomposition, which is what extracting the theta subgraph would need.

## Main results

* `Monophilic.choosable_two_of_rubinFamily` — Rubin's ⟸ direction
* `SimpleGraph.monophilic_two_iff_of_rubin_hard` — Theorem 2, borrowing only Rubin's ⟹ direction
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
