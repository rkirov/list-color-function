/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.ThetaClass
import Monophilic.K23
import Monophilic.ListColorFunction
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Theorem 2 of Kirov–Naimi, with a concrete notion of core

**Kirov–Naimi 2016**, *List coloring and `n`-monophilic graphs*, Ars Combin. **124** (2016),
329–340 (arXiv:1004.5183), Theorem 2, states verbatim:

> **Theorem 2.** A connected graph is 2-monophilic iff its core is a single vertex, is a cycle, is
> `K₂,₃`, or contains an odd cycle.

The same statement appears as Theorem 2(iv) of Chi, Lee, Morrissette, Mudrock, Nguyen and Whatley
(arXiv:2605.10861, 2026), there attributed to [1, 6, 13, 16, 17] with Kirov–Naimi as [16].

This file states it with the four alternatives as **real definitions** rather than abstract
propositions, and proves it from one hypothesis: **Rubin's theorem** (`Monophilic.RubinTheorem`),
which is not yet available in this development — it is being proved in `Monophilic/RubinHard.lean`.
The hypothesis is the *first explicit argument* of `Monophilic.monophilic_two_iff_of_rubin`, so that
the day a term `rubinTheorem : RubinTheorem` exists, `monophilic_two_iff_of_rubin rubinTheorem` is
the unconditional theorem with no other edit anywhere.

## What "core" means here

The **core** of a graph, in the paper's sense, is what remains after repeatedly deleting vertices of
degree one. Read backwards, "the core of `G` is `H`" says that `G` is `H` with a finite tower of
pendant vertices attached, which is exactly `SimpleGraph.pendantTower` from `Monophilic.Core`. That
is the definition used here (`Monophilic.CoreIs`), and the four alternatives of Theorem 2 and the
three of Rubin's theorem are spelled out on top of it.

This presentation is **mechanization, not mathematics**: the paper simply says "core", and the
tower formulation is a device for naming the intermediate vertex types without constructing a
quotient. Kirov–Naimi's Lemma 5 (`SimpleGraph.monophilic_pendantTower_iff`) is what makes the two
readings interchangeable, and it is the paper's, not ours.

### A parity convention that bites

`Monophilic.closePath k` is the cycle on `k + 1` vertices. So `Odd k` picks out the cycles on an
**even** number of vertices, and `Even k` the **odd** cycles. Every statement below is checked
numerically on small cases before it is used; see the `#guard`s in the "Sanity checks" section.

## What is proved unconditionally

Rubin's theorem is used in exactly one place. Everything else is earned here:

* the whole **⟸ direction** of Theorem 2 (`Monophilic.monophilic_two_of_alternatives`);
* in the **⟹ direction**, the case where `G` is *not* `2`-colorable
  (`Monophilic.hasOddCycle_of_not_colorable_two`: a graph that is not `2`-colorable contains an odd
  cycle — the converse of the easy bridge, and the one ingredient of the paper's proof that Mathlib
  did not have);
* in the **⟹ direction**, the reduction of the `2`-colorable case to Rubin's *conclusion*
  (`Monophilic.alternatives_of_rubinAlternatives`), which consumes the three-way disjunction and
  produces the four-way one without assuming Rubin;
* the **⟸ direction of Rubin's theorem** itself
  (`Monophilic.choosable_two_of_rubinAlternatives`), so the content still missing from
  `RubinTheorem` is only its forward implication.

## Main definitions

* `Monophilic.CoreIs G H` : the core of `G` is `H` — `G` is `H` with a pendant tower attached
* `Monophilic.CoreIsVertex`, `Monophilic.CoreIsCycle`, `Monophilic.CoreIsK23` : three of the four
  alternatives of Theorem 2; the fourth is `Monophilic.HasOddCycle`
* `Monophilic.CoreIsEvenCycle`, `Monophilic.CoreIsTheta` : the other two alternatives of Rubin's
  theorem
* `Monophilic.RubinTheorem` : Rubin's theorem, as a proposition

## Main results

* `SimpleGraph.monophilic_of_forall_not_adj` : an edgeless graph is `n`-monophilic
* `Monophilic.not_colorable_of_contains` : non-`n`-colorability passes from a subgraph upwards
* `Monophilic.exists_odd_isCycle_of_odd_closed_walk` : an odd closed walk contains an odd cycle
* `Monophilic.hasOddCycle_of_not_colorable_two` : **a graph that is not `2`-colorable contains an
  odd cycle**
* `Monophilic.monophilic_two_of_alternatives` : the ⟸ direction of Theorem 2
* `Monophilic.alternatives_of_rubinAlternatives` : the ⟹ direction, `2`-colorable case
* `Monophilic.monophilic_two_iff_of_rubin` : **Theorem 2 of Kirov–Naimi**
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **An edgeless graph is `n`-monophilic**, for every `n`: every list assignment, constant or not,
admits exactly `∏ v, |L v|` colorings, and for an `n`-list assignment that is `n ^ |V|` either way.

Not from the literature — a bookkeeping lemma. It is used only for the degenerate first alternative
of Theorem 2, the one-vertex core. Compare `SimpleGraph.choosable_of_forall_not_adj`. -/
theorem monophilic_of_forall_not_adj {n : ℕ} (h : ∀ a b, ¬ G.Adj a b) : G.Monophilic n := by
  have hprop : ∀ f : V → ℕ, G.IsProperColoring f := fun f a b hab => absurd hab (h a b)
  have key : ∀ M : ListAssignment V, G.col M = ∏ v, (M v).card := by
    intro M
    rw [col, colorings, Finset.filter_true_of_mem (fun f _ => hprop f), Fintype.card_piFinset]
  intro L hL
  rw [colConst, key, key]
  exact le_of_eq (Finset.prod_congr rfl fun v _ => by rw [hL v]; simp)

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-! ### Odd cycles

The paper's proof of Theorem 2 opens with "If `G` is not 2-colorable, then it must contain an odd
cycle". That is the classical characterization of bipartite graphs, which Mathlib lists as a `TODO`
in `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`; it is proved here.

Two of the three steps are Mathlib's: `SimpleGraph.two_colorable_iff_forall_loop_even` turns the
failure of `2`-colorability into an odd closed *walk*, and `SimpleGraph.cycleGraph_isContained_iff`
turns a cycle *walk* into a subgraph copy of `SimpleGraph.cycleGraph`. The middle step — extracting
an odd *cycle* from an odd closed walk — is `Monophilic.exists_odd_isCycle_of_odd_closed_walk`
below, and the translation between `SimpleGraph.cycleGraph` and this development's
`Monophilic.closePath` is `Monophilic.contains_closePath_of_isContained_cycleGraph`. -/

/-- **Non-`n`-colorability passes from a subgraph to the whole graph.** Restrict a coloring along
the embedding; adjacent vertices of the subgraph stay adjacent, so they stay differently colored.

Not from the literature — the colorability analogue of
`Monophilic.not_choosable_of_contains`. -/
theorem not_colorable_of_contains {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj] {K : SimpleGraph W}
    [DecidableRel K.Adj] {n : ℕ} (hK : ¬ K.Colorable n) (h : Contains G K) : ¬ G.Colorable n := by
  obtain ⟨f, _, hadj⟩ := h
  rintro ⟨c⟩
  exact hK ⟨Coloring.mk (fun w => c (f w)) fun {a b} hab => c.valid (hadj a b hab)⟩

/-- **An odd closed walk contains an odd cycle.**

Classical folklore, not attributable to any particular paper, and not in Mathlib — it is the middle
step of "not bipartite ⟹ has an odd cycle", which
`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` records as a `TODO`. The proof below is the
standard textbook argument, mechanized here.

By strong induction on the length. An odd closed walk has length at least three: length
one would be a loop, which a simple graph does not have. If the walk is already a cycle we are
done. Otherwise some vertex `y` occurs twice along it; rotate the walk to be based at `y`
(`SimpleGraph.Walk.rotate`) and cut it at the *second* visit to `y`
(`SimpleGraph.Walk.takeUntil` / `SimpleGraph.Walk.dropUntil`). This splits it into two strictly
shorter closed walks at `y` whose lengths sum to the original, so exactly one of them is odd. -/
theorem exists_odd_isCycle_of_odd_closed_walk {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (n : ℕ) : ∀ {x : V} (w : G.Walk x x), w.length = n → Odd n →
      ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ Odd c.length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x w hlen hodd
    -- an odd closed walk has length at least three: length one would be a loop
    have hne1 : n ≠ 1 := by
      intro h1
      have hadj := w.adj_getVert_succ (i := 0) (by omega)
      rw [Walk.getVert_zero, show (0 : ℕ) + 1 = w.length by omega, Walk.getVert_length] at hadj
      exact hadj.ne rfl
    have h3 : 3 ≤ n := by obtain ⟨t, ht⟩ := hodd; omega
    by_cases hcyc : w.IsCycle
    · exact ⟨x, w, hcyc, hlen ▸ hodd⟩
    -- not a cycle: some vertex `y` is visited twice
    have hnil : ¬ w.Nil := by rw [Walk.not_nil_iff_lt_length]; omega
    have hnp : ¬ w.tail.IsPath := fun hp =>
      hcyc (Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨hp, by omega⟩)
    rw [Walk.isPath_def] at hnp
    obtain ⟨y, hy⟩ : ∃ y, 2 ≤ w.tail.support.count y := by
      by_contra hcon
      push Not at hcon
      exact hnp (List.nodup_iff_count_le_one.mpr fun a => by have := hcon a; omega)
    rw [Walk.support_tail_of_not_nil w hnil] at hy
    have hymem : y ∈ w.support := List.tail_subset _ (List.count_pos_iff.mp (by omega))
    -- rotate the walk so that it is based at `y`
    obtain ⟨w', hlen', hy'⟩ :
        ∃ w' : G.Walk y y, w'.length = n ∧ 2 ≤ w'.support.tail.count y :=
      ⟨w.rotate y hymem, by rw [Walk.length_rotate]; exact hlen,
        by rw [(Walk.support_rotate w y hymem).perm.count_eq y]; exact hy⟩
    have hnil' : ¬ w'.Nil := by rw [Walk.not_nil_iff_lt_length]; omega
    rw [← Walk.support_tail_of_not_nil w' hnil'] at hy'
    have hyq : y ∈ w'.tail.support := List.count_pos_iff.mp (by omega)
    -- cut at the second visit to `y`: two strictly shorter closed walks at `y`
    obtain ⟨r, s, hsum, hs1⟩ :
        ∃ (r : G.Walk w'.snd y) (s : G.Walk y y),
          r.length + 1 + s.length = n ∧ 1 ≤ s.length := by
      refine ⟨w'.tail.takeUntil y hyq, w'.tail.dropUntil y hyq, ?_, ?_⟩
      · have h1 := congrArg Walk.length (w'.tail.take_spec hyq)
        rw [Walk.length_append] at h1
        have h2 : w'.tail.length + 1 = w'.length := Walk.length_tail_add_one hnil'
        omega
      · have hcount : w'.tail.support.count y
            = 1 + ((w'.tail.dropUntil y hyq).support.tail).count y := by
          conv_lhs => rw [← w'.tail.take_spec hyq]
          rw [Walk.support_append, List.count_append,
            w'.tail.count_support_takeUntil_eq_one hyq]
        have h2 := List.count_le_length (a := y) (l := (w'.tail.dropUntil y hyq).support.tail)
        have h3' : ((w'.tail.dropUntil y hyq).support.tail).length
            = (w'.tail.dropUntil y hyq).length := by
          rw [List.length_tail, Walk.length_support]; omega
        omega
    -- exactly one of the two halves is odd, and both are shorter
    rw [Nat.odd_iff] at hodd
    by_cases hpar : (r.length + 1) % 2 = 1
    · exact ih _ (by omega) (Walk.cons (Walk.adj_snd hnil') r) (by simp) (Nat.odd_iff.mpr hpar)
    · exact ih _ (by omega) s rfl (Nat.odd_iff.mpr (by omega))

/-- The numbering `Monophilic.pathVtx` identifies `closePath (k+1)` with Mathlib's
`SimpleGraph.cycleGraph (k+2)`: cyclically consecutive indices on one side, indices differing by
one in `Fin (k+2)` on the other. Only the direction needed below is recorded. -/
private theorem cycleGraph_adj_of_closePath_adj {k : ℕ} {a b : PathV (k + 1)}
    (h : (closePath (k + 1)).Adj a b) :
    (cycleGraph (k + 2)).Adj ((pathVtxEquiv (k + 1)).symm a) ((pathVtxEquiv (k + 1)).symm b) := by
  obtain ⟨i, rfl⟩ := exists_fin_pathVtx (k + 1) a
  obtain ⟨j, rfl⟩ := exists_fin_pathVtx (k + 1) b
  have hi : (pathVtxEquiv (k + 1)).symm (pathVtx (k + 1) i.val) = i :=
    (pathVtxEquiv (k + 1)).symm_apply_apply i
  have hj : (pathVtxEquiv (k + 1)).symm (pathVtx (k + 1) j.val) = j :=
    (pathVtxEquiv (k + 1)).symm_apply_apply j
  rw [hi, hj, cycleGraph_adj]
  rcases (closePath_adj_pathVtx_fin (by omega) i j).mp h with h1 | h1
  · exact Or.inr (by rw [← h1]; simp)
  · exact Or.inl (by rw [← h1]; simp)

/-- A copy of Mathlib's `SimpleGraph.cycleGraph (k+2)` is a copy of this development's
`Monophilic.closePath (k+1)`: the two are the same cycle, numbered differently.

Not from the literature — a translation between two models of the same graph. -/
theorem contains_closePath_of_isContained_cycleGraph {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (h : cycleGraph (k + 2) ⊑ G) :
    Contains G (closePath (k + 1)) := by
  obtain ⟨f⟩ := h
  exact ⟨fun v => f.toHom ((pathVtxEquiv (k + 1)).symm v),
    f.injective.comp (pathVtxEquiv (k + 1)).symm.injective,
    fun _ _ hab => f.toHom.map_adj (cycleGraph_adj_of_closePath_adj hab)⟩

/-- **`G` contains an odd cycle**: a subgraph copy of a cycle on an odd number of vertices.

`closePath k` is the cycle on `k + 1` vertices, so `Even k` is what makes it odd. -/
def HasOddCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Prop :=
  ∃ k, Even k ∧ 2 ≤ k ∧ Contains G (closePath k)

/-- **A graph containing an odd cycle is not `2`-colorable.** Classical and elementary; the easy
half of the bipartite characterization. An odd cycle is not `2`-colorable
(`Monophilic.not_colorable_two_closePath_of_even`, itself a corollary of Kirov–Naimi's Theorem 1 in
this development) and non-colorability passes upwards. -/
theorem not_colorable_two_of_hasOddCycle {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : HasOddCycle G) : ¬ G.Colorable 2 := by
  obtain ⟨k, hk, hk2, hcon⟩ := h
  exact not_colorable_of_contains (not_colorable_two_closePath_of_even hk hk2) hcon

/-- **A graph that is not `2`-colorable contains an odd cycle.**

Not from the literature as a Lean statement — this is the classical characterization of bipartite
graphs, which Mathlib records as an open `TODO`. It is the one ingredient of Kirov–Naimi's proof of
Theorem 2 ("If `G` is not 2-colorable, then it must contain an odd cycle") that had to be built
from scratch here. No connectivity hypothesis is needed. -/
theorem hasOddCycle_of_not_colorable_two {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : ¬ G.Colorable 2) : HasOddCycle G := by
  rw [two_colorable_iff_forall_loop_even] at h
  push Not at h
  obtain ⟨u, w, hw⟩ := h
  rw [Nat.not_even_iff_odd] at hw
  obtain ⟨y, c, hcyc, hodd⟩ := exists_odd_isCycle_of_odd_closed_walk w.length w rfl hw
  have h3 : 3 ≤ c.length := hcyc.three_le_length
  obtain ⟨j, hj⟩ : ∃ j, c.length = j + 2 := ⟨c.length - 2, by omega⟩
  refine ⟨j + 1, ?_, by omega, ?_⟩
  · obtain ⟨t, ht⟩ := hodd
    rw [Nat.even_iff]
    omega
  · exact contains_closePath_of_isContained_cycleGraph
      ((cycleGraph_isContained_iff (by omega)).mpr ⟨y, c, hcyc, hj⟩)

/-! ### The core, and the alternatives of Theorem 2 and of Rubin's theorem

Mechanization, not mathematics: the paper says "core", and this is how that word is spelled in
Lean. -/

/-- **The core of `G` is `H`**: `G` is `H` with a finite tower of pendant vertices attached.

Kirov–Naimi's core is obtained from `G` by deleting vertices of degree one until none remain. Read
in reverse, that says `G` is built from its core by attaching pendant vertices one at a time, each
one at an arbitrary vertex of the graph built so far — which is `SimpleGraph.pendantTower`. The
statement is up to isomorphism because the tower lives on its own vertex type.

This definition is **mechanization**, not part of Kirov–Naimi: the paper simply says "core".
Kirov–Naimi's **Lemma 5** (`SimpleGraph.monophilic_pendantTower_iff`) is what makes the two
readings interchangeable for monophilicity, and its choosability analogue
(`SimpleGraph.choosable_pendantTower_iff`) does the same for choosability. -/
def CoreIs {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∃ (k : ℕ) (d : TowerData W k), Nonempty (G ≃g pendantTower H k d)

section CoreTransport

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- **A graph is `n`-monophilic exactly when its core is.** This is Kirov–Naimi's **Lemma 5**,
transported across the isomorphism in `Monophilic.CoreIs`. -/
theorem monophilic_iff_of_coreIs (h : CoreIs G H) (n : ℕ) : G.Monophilic n ↔ H.Monophilic n := by
  obtain ⟨k, d, ⟨e⟩⟩ := h
  letI := instDecidableEqTowerV (V := W) k
  letI := instFintypeTowerV (V := W) k
  letI := instDecidableRelPendantTower (G := H) k d
  exact (monophilic_iso e n).trans (monophilic_pendantTower_iff n k d)

/-- **A graph is `n`-choosable exactly when its core is**, for `n ≥ 2`: the choosability analogue
of Kirov–Naimi's Lemma 5, and the "core" half of Rubin's theorem. -/
theorem choosable_iff_of_coreIs (h : CoreIs G H) {n : ℕ} (hn : 2 ≤ n) :
    G.Choosable n ↔ H.Choosable n := by
  obtain ⟨k, d, ⟨e⟩⟩ := h
  letI := instDecidableEqTowerV (V := W) k
  letI := instFintypeTowerV (V := W) k
  letI := instDecidableRelPendantTower (G := H) k d
  exact (choosable_iso e n).trans (choosable_pendantTower_iff hn k d)

end CoreTransport

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! The six alternatives below — four from Theorem 2, three from Rubin's theorem, sharing the
one-vertex case — are **mechanization**, not mathematics: each spells out on top of
`Monophilic.CoreIs` a phrase the two papers state in words. -/

/-- **The core of `G` is a single vertex.** `Monophilic.pathG 0` is the one-vertex graph — a path of
length zero. Equivalently, `G` is a tree. First alternative of Theorem 2, and of Rubin's theorem. -/
def CoreIsVertex : Prop := CoreIs G (pathG 0)

/-- **The core of `G` is a cycle.** `closePath k` is the cycle on `k + 1` vertices, and `2 ≤ k`
says it really is a cycle rather than a point or a single edge. No parity restriction: Theorem 2
says "is a cycle", not "is an even cycle". Second alternative of Theorem 2. -/
def CoreIsCycle : Prop := ∃ k, 2 ≤ k ∧ CoreIs G (closePath k)

/-- **The core of `G` is an even cycle**, i.e. a cycle on an even number of vertices. Since
`closePath k` has `k + 1` vertices, that is `Odd k`. Second alternative of Rubin's theorem. -/
def CoreIsEvenCycle : Prop := ∃ k, Odd k ∧ 2 ≤ k ∧ CoreIs G (closePath k)

/-- **The core of `G` is `K₂,₃`.** `Monophilic.theta 1` is `θ_{2,2,2}`, which is `K₂,₃`; the
isomorphism is `Monophilic.k23IsoThetaOne`. Third alternative of Theorem 2. -/
def CoreIsK23 : Prop := CoreIs G (theta 1)

/-- **The core of `G` is `θ_{2,2,2m}` for some `m ≥ 1`.** Third alternative of Rubin's theorem. -/
def CoreIsTheta : Prop := ∃ m, 1 ≤ m ∧ CoreIs G (theta m)

/-! ### Rubin's theorem -/

/-- **Rubin's theorem.**

> A connected graph is `2`-choosable iff its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

Due to **A. L. Rubin**, and published in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in
graphs*, Congr. Numer. **26** (1979), 125–157. Kirov–Naimi's proof of Theorem 2 uses it.

It is **not yet proved in this development**; the proof is being built in
`Monophilic/RubinHard.lean`. Until it lands, `Monophilic.monophilic_two_iff_of_rubin` takes a term
of this type as its first explicit argument. The `↔` form is the form the argument is stated in;
its ⟸ half is already proved here, as `Monophilic.choosable_two_of_rubinAlternatives`, so what is
outstanding is only the forward implication. -/
def RubinTheorem : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (G.Choosable 2 ↔ (CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G))

/-! ### The pieces of Theorem 2 that need no hypothesis -/

variable {G}

/-- **`K₂,₃` and `θ_{2,2,2}` are the same graph**, on the two models this development uses: an
explicit bijection, checked by `decide`. Bookkeeping, not mathematics. -/
def k23IsoThetaOne : completeBipartiteGraph (Fin 2) (Fin 3) ≃g theta 1 where
  toEquiv :=
    { toFun := Sum.elim ![some (some none), some (some (some (some ())))]
        ![none, some none, some (some (some none))]
      invFun := fun v => match v with
        | none => Sum.inr 0
        | some none => Sum.inr 1
        | some (some none) => Sum.inl 0
        | some (some (some none)) => Sum.inr 2
        | some (some (some (some _))) => Sum.inl 1
      left_inv := by decide
      right_inv := by decide }
  map_rel_iff' := by decide

/-- **`θ_{2,2,2} = K₂,₃` is `2`-monophilic.** This is Kirov–Naimi's **Lemma 6**
(`SimpleGraph.monophilic_K23`), moved onto the theta model. -/
theorem monophilic_two_theta_one : (theta 1).Monophilic 2 :=
  (monophilic_iso k23IsoThetaOne 2).mp monophilic_K23

/-- **The one-vertex graph is `n`-monophilic.** It has no edges. Not from the literature — the
degenerate case, which Kirov–Naimi dispose of with the word "clearly". -/
theorem monophilic_pathG_zero (n : ℕ) : (pathG 0).Monophilic n :=
  monophilic_of_forall_not_adj fun _ _ h => h

/-- A graph whose core is a single vertex is `2`-monophilic — indeed `n`-monophilic for every `n`.
By Kirov–Naimi's **Lemma 5** it suffices that the core is, and a one-vertex graph has no edges. -/
theorem monophilic_of_coreIsVertex (h : CoreIsVertex G) (n : ℕ) : G.Monophilic n :=
  (monophilic_iff_of_coreIs h n).mpr (monophilic_pathG_zero n)

/-- A graph whose core is a cycle is `2`-monophilic — indeed `n`-monophilic for every `n`. This is
Kirov–Naimi's **Theorem 1** (`Monophilic.monophilic_closePath_all`: every cycle is `n`-monophilic)
together with **Lemma 5**. Note that no parity hypothesis is needed: *every* cycle is
`n`-monophilic, which is why Theorem 2 says "is a cycle" where Rubin's theorem says "is an even
cycle". -/
theorem monophilic_of_coreIsCycle (h : CoreIsCycle G) (n : ℕ) : G.Monophilic n := by
  obtain ⟨k, hk2, hc⟩ := h
  exact (monophilic_iff_of_coreIs hc n).mpr (monophilic_closePath_all k n hk2)

/-- A graph whose core is `K₂,₃` is `2`-monophilic. Kirov–Naimi's **Lemma 6** together with
**Lemma 5**. -/
theorem monophilic_two_of_coreIsK23 (h : CoreIsK23 G) : G.Monophilic 2 :=
  (monophilic_iff_of_coreIs h 2).mpr monophilic_two_theta_one

/-- A graph containing an odd cycle is `2`-monophilic, vacuously: it is not `2`-colorable, so it has
no colorings at all from the constant list of two colors. This is item (2) of the three regimes on
p. 2 of Kirov–Naimi (`SimpleGraph.monophilic_of_not_colorable`). -/
theorem monophilic_two_of_hasOddCycle (h : HasOddCycle G) : G.Monophilic 2 :=
  monophilic_of_not_colorable (not_colorable_two_of_hasOddCycle h)

/-- **The ⟸ direction of Kirov–Naimi's Theorem 2, unconditionally.** A graph whose core is a single
vertex, a cycle or `K₂,₃`, or which contains an odd cycle, is `2`-monophilic.

This is the direction the paper disposes of in two sentences: "Clearly a single vertex and a graph
that contains an odd cycle are both 2-monophilic. Also, by Theorem 1 and Lemma 6, all cycles and
`K₂,₃` are 2-monophilic. Using Lemma 5, this gives us one direction of the theorem." Nothing is
assumed here — in particular Rubin's theorem is not used, and neither is connectivity. -/
theorem monophilic_two_of_alternatives
    (h : CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G) : G.Monophilic 2 := by
  rcases h with h | h | h | h
  · exact monophilic_of_coreIsVertex h 2
  · exact monophilic_of_coreIsCycle h 2
  · exact monophilic_two_of_coreIsK23 h
  · exact monophilic_two_of_hasOddCycle h

/-- **The ⟸ direction of Rubin's theorem, unconditionally**: a graph whose core is a single vertex,
an even cycle or a `θ_{2,2,2m}` is `2`-choosable.

Due to **A. L. Rubin** (Erdős–Rubin–Taylor 1979); the Lean proof rests on
`Monophilic.choosable_two_of_rubinFamily`, itself a corollary of Kirov–Naimi's Theorem 1 in the
even-cycle case. Recording it here pins down that the content still missing from
`Monophilic.RubinTheorem` is only its **forward** implication. -/
theorem choosable_two_of_rubinAlternatives
    (h : CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G) : G.Choosable 2 := by
  rcases h with h | ⟨k, hk, hk2, hc⟩ | ⟨m, hm, hc⟩
  · exact (choosable_iff_of_coreIs h le_rfl).mpr
      (letI : Subsingleton (PathV 0) := inferInstanceAs (Subsingleton Unit)
       choosable_of_subsingleton one_le_two)
  · exact (choosable_iff_of_coreIs hc le_rfl).mpr
      (choosable_two_of_rubinFamily _ (Or.inr (Or.inl ⟨k, hk, hk2, ⟨Iso.refl⟩⟩)))
  · exact (choosable_iff_of_coreIs hc le_rfl).mpr
      (choosable_two_of_rubinFamily _ (Or.inr (Or.inr ⟨m, hm, ⟨Iso.refl⟩⟩)))

/-- **The ⟹ direction of Kirov–Naimi's Theorem 2 in the `2`-colorable case, unconditionally.**

Given that `G` is `2`-monophilic and that Rubin's *conclusion* holds for it — its core is a single
vertex, an even cycle or a `θ_{2,2,2m}` — the four alternatives of Theorem 2 follow. This is the
last sentence of the paper's proof: "So, by Rubin's theorem above, it is enough to show that for
`m ≥ 2`, `θ_{2,2,2m}` is not 2-monophilic."

Rubin's theorem is *not* assumed here; its conclusion is taken as a hypothesis, so that the only
place `Monophilic.RubinTheorem` is consumed in this file is
`Monophilic.monophilic_two_iff_of_rubin`. The two moving parts are the collapse of "even cycle" into
"cycle" — Theorem 2 asks for less — and the elimination of `θ_{2,2,2m}` for `m ≥ 2` by
`Monophilic.not_monophilic_theta`, leaving `m = 1`, which is `K₂,₃`. -/
theorem alternatives_of_rubinAlternatives (hmono : G.Monophilic 2)
    (h : CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G) :
    CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G := by
  rcases h with h | ⟨k, _, hk2, hc⟩ | ⟨m, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨k, hk2, hc⟩)
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      exact Or.inr (Or.inr (Or.inl hc))
    · exact absurd ((monophilic_iff_of_coreIs hc 2).mp hmono) (not_monophilic_theta m hm2)

/-! ### Theorem 2 -/

/-- **Theorem 2 of Kirov–Naimi.**

> A connected graph is 2-monophilic iff its core is a single vertex, is a cycle, is `K₂,₃`, or
> contains an odd cycle.

**Kirov–Naimi 2016**, *List coloring and `n`-monophilic graphs*, Ars Combin. **124** (2016),
329–340 (arXiv:1004.5183), Theorem 2. It appears again as Theorem 2(iv) of Chi, Lee, Morrissette,
Mudrock, Nguyen and Whatley (arXiv:2605.10861, 2026), there attributed to [1, 6, 13, 16, 17] with
Kirov–Naimi as [16].

The single hypothesis `rubin` is **Rubin's theorem** (A. L. Rubin, in Erdős–Rubin–Taylor,
*Choosability in graphs*, Congr. Numer. **26** (1979), 125–157), which this development is in the
course of proving in `Monophilic/RubinHard.lean`. It is the *first explicit argument*, so that
`monophilic_two_iff_of_rubin rubinTheorem` becomes the unconditional theorem the moment such a term
exists, with no other change. Nothing else is assumed.

The proof follows the paper. The ⟸ direction is `Monophilic.monophilic_two_of_alternatives`. For
⟹: if `G` is not `2`-colorable it contains an odd cycle
(`Monophilic.hasOddCycle_of_not_colorable_two`); otherwise `2`-monophilicity plus `2`-colorability
gives `2`-choosability (`SimpleGraph.choosable_of_monophilic_of_colorable`), Rubin's theorem applies
to the connected graph `G`, and `Monophilic.alternatives_of_rubinAlternatives` converts its
conclusion into the four alternatives.

**Connectivity is load-bearing in exactly one place**: it is the hypothesis of Rubin's theorem, and
it is used nowhere else. Every other step above holds for an arbitrary finite graph. -/
theorem monophilic_two_iff_of_rubin (rubin : RubinTheorem) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) :
    G.Monophilic 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G := by
  refine ⟨fun hmono => ?_, monophilic_two_of_alternatives⟩
  by_cases hcol : G.Colorable 2
  · exact alternatives_of_rubinAlternatives hmono
      ((rubin G hconn).mp (choosable_of_monophilic_of_colorable hmono hcol))
  · exact Or.inr (Or.inr (Or.inr (hasOddCycle_of_not_colorable_two hcol)))

/-! ### Sanity checks

The parity convention is the one place where an off-by-one is invisible to the type checker, so it
is pinned down numerically. `closePath k` is the cycle on `k + 1` vertices: `Even k` gives an
**odd** cycle (no `2`-coloring at all) and `Odd k` an **even** one (exactly two). -/

section Guards

#guard Fintype.card (PathV 2) = 3
#guard (closePath 2).edgeFinset.card = 3

-- `Even k` ⇒ odd cycle ⇒ `col(C, 2) = 0`; `Odd k` ⇒ even cycle ⇒ `col(C, 2) = 2`
#guard (closePath 2).colConst 2 = 0      -- `C₃`
#guard (closePath 3).colConst 2 = 2      -- `C₄`
#guard (closePath 4).colConst 2 = 0      -- `C₅`
#guard (closePath 5).colConst 2 = 2      -- `C₆`
#guard [2, 3, 4, 5, 6, 7].all fun k =>
  ((closePath k).colConst 2 == 0) == decide (Even k)

-- `theta 1` really is `K₂,₃`: five vertices, six edges, degree sequence `2,2,3,2,3`
#guard Fintype.card (ThetaV 1) = 5
#guard (theta 1).edgeFinset.card = 6
#guard (completeBipartiteGraph (Fin 2) (Fin 3)).edgeFinset.card = 6
#guard (univ : Finset (ThetaV 1)).val.map (fun v => (theta 1).degree v) = {2, 2, 3, 2, 3}
#guard ∀ a : Fin 2 ⊕ Fin 3, ∀ b : Fin 2 ⊕ Fin 3,
  ((theta 1).Adj (k23IsoThetaOne a) (k23IsoThetaOne b)
    ↔ (completeBipartiteGraph (Fin 2) (Fin 3)).Adj a b)

-- `theta m` for `m ≥ 2` is *not* `K₂,₃`, and is where the two theorems part company
#guard Fintype.card (ThetaV 2) = 7
#guard (theta 2).colConst 2 = 2

end Guards

end Monophilic

#print axioms SimpleGraph.monophilic_of_forall_not_adj
#print axioms Monophilic.not_colorable_of_contains
#print axioms Monophilic.exists_odd_isCycle_of_odd_closed_walk
#print axioms Monophilic.contains_closePath_of_isContained_cycleGraph
#print axioms Monophilic.not_colorable_two_of_hasOddCycle
#print axioms Monophilic.hasOddCycle_of_not_colorable_two
#print axioms Monophilic.monophilic_iff_of_coreIs
#print axioms Monophilic.choosable_iff_of_coreIs
#print axioms Monophilic.monophilic_two_theta_one
#print axioms Monophilic.monophilic_pathG_zero
#print axioms Monophilic.monophilic_of_coreIsVertex
#print axioms Monophilic.monophilic_of_coreIsCycle
#print axioms Monophilic.monophilic_two_of_coreIsK23
#print axioms Monophilic.monophilic_two_of_hasOddCycle
#print axioms Monophilic.monophilic_two_of_alternatives
#print axioms Monophilic.choosable_two_of_rubinAlternatives
#print axioms Monophilic.alternatives_of_rubinAlternatives
#print axioms Monophilic.monophilic_two_iff_of_rubin
