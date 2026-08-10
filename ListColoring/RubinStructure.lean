/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.TwoCycles

/-!
# Rubin's structural argument: bridging Mathlib's cycles to the index form

**Attribution.** Everything in this file serves the hard direction of **Rubin's theorem**
(A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West Coast
Conf. on Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congr. Numer. **26**,
Utilitas Math., Winnipeg, **1980**, 125–157, pp. 131–134). Nothing here is novel; the content of
this file in particular is **mechanization**, not mathematics — it converts between two encodings of
"a cycle" that a paper would not distinguish.

## Why this file exists

`ListColoring.TwoCycles` states its non-choosability results over cycles presented as **index
sequences** — a function `A : ℕ → V` with `G.Adj (A i) (A (i+1))` for `i < m` and `G.Adj (A m)
(A 0)` — because that is what the colour-forcing chains are written against. Mathlib presents a
cycle as a `SimpleGraph.Walk` together with `Walk.IsCycle`. Rubin's argument produces the latter, so
something has to convert.

That conversion is this file: for `c : G.Walk v v` with `hc : c.IsCycle`, take `A := c.getVert` and
`m := c.length - 1`, and supply the three facts the dumbbell and figure-eight results need —
adjacency along the cycle, closure at the end, and injectivity.

## The proof this feeds

Rubin's five types, and where each is discharged:

1. an odd cycle — `ListColoring.not_choosable_two_of_contains_odd_cycle`;
2. two node-disjoint even cycles joined by a path — `ListColoring.not_choosable_two_of_dumbbell`;
3. two even cycles sharing exactly one node — `ListColoring.not_choosable_two_of_figureEight`;
4. `θ_{a,b,c}` with `a ≠ 2` and `b ≠ 2` — `ListColoring.choosable_two_gtheta_iff`;
5. a generalized theta on four or more arms — `ListColoring.not_choosable_two_gtheta_of_four`.

All five are **proved**. What remains of the hard direction is the *structural extraction*: that a
core not in `{K₁, C_{2m+2}, θ_{2,2,2m}}` contains one of the five. See `plan.md` for the plan, taken
from Rubin's own argument, which runs on a shortest cycle and two shortest connecting paths and
needs **no** ear decomposition, Menger, or 2-connectivity.

## Main results

* `ListColoring.cycleWalk_adj` — adjacency along a cycle walk, in index form
* `ListColoring.cycleWalk_closes` — the closing edge
* `ListColoring.cycleWalk_injOn` — injectivity on `Set.Iic (c.length - 1)`
* `ListColoring.two_le_cycleWalk_bound` — a cycle has `2 ≤ c.length - 1`
* `ListColoring.not_choosable_two_of_two_cycle_walks` — types 2 and 3, from Mathlib cycles
* `ListColoring.exists_isCycle_of_two_le_degree` — E1: a connected graph of minimum degree `≥ 2` has
  a cycle
* `ListColoring.exists_shortest_isCycle` — E1: and a shortest one, which is Rubin's `C₁`
* `ListColoring.exists_connecting_path` — E2: Rubin's connecting path, for an arbitrary set of
  vertices and set of already-used edges
* `ListColoring.exists_connecting_path_of_cycle` — E2 as Rubin states it, for a cycle `C₁`
* `ListColoring.not_choosable_two_of_cycles_meet_le_one` — Rubin's step 3, from Mathlib's cycles
* `ListColoring.exists_connecting_path_of_choosable`,
  `ListColoring.exists_connecting_path_of_cycle_of_choosable` — E2 with its cycle hypothesis
  replaced by `2`-choosability, which is the form Rubin's steps 4 and 5 use
-/

namespace ListColoring

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The bridge

A cycle walk `c : G.Walk v v` of length `L` visits `L` distinct vertices, `c.getVert 0, …,
c.getVert (L-1)`, and closes because `c.getVert L = v = c.getVert 0`. So the index form takes
`A := c.getVert` and `m := L - 1`. Mechanization only. -/

/-- A cycle has length at least `3`, so the index bound `m = length - 1` is at least `2` — which is
the hypothesis `ListColoring.not_choosable_two_of_dumbbell` asks for. -/
theorem two_le_cycleWalk_bound {v : V} {c : G.Walk v v} (hc : c.IsCycle) : 2 ≤ c.length - 1 := by
  have := hc.three_le_length
  omega

/-- Consecutive vertices of a cycle walk are adjacent, indexed from `0`. -/
theorem cycleWalk_adj {v : V} (c : G.Walk v v) {i : ℕ} (hi : i < c.length - 1) :
    G.Adj (c.getVert i) (c.getVert (i + 1)) :=
  c.adj_getVert_succ (by omega)

/-- The closing edge of a cycle walk: the last distinct vertex is adjacent to the first. -/
theorem cycleWalk_closes {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    G.Adj (c.getVert (c.length - 1)) (c.getVert 0) := by
  have h3 := hc.three_le_length
  have hadj := c.adj_getVert_succ (i := c.length - 1) (by omega)
  have hlen : c.length - 1 + 1 = c.length := by omega
  rw [hlen, c.getVert_length] at hadj
  rw [c.getVert_zero]
  exact hadj

/-- A cycle walk visits `c.length` distinct vertices: `getVert` is injective on `Set.Iic
(c.length - 1)`. This is Mathlib's `SimpleGraph.Walk.IsCycle.getVert_injOn'`, restated with
`Set.Iic` so that it matches `ListColoring.not_choosable_two_of_dumbbell`. -/
theorem cycleWalk_injOn {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    Set.InjOn c.getVert (Set.Iic (c.length - 1)) :=
  hc.getVert_injOn'

/-! ### E1 — a core contains a cycle

Rubin's argument opens by taking a **shortest cycle** `C₁` in the core. That presupposes a cycle
exists, which is where minimum degree `≥ 2` is used, and it is the one thing in this step Mathlib
does not already supply.

The proof is a count rather than the usual longest-path argument: a connected acyclic graph is a
tree, so it has `n - 1` edges, while minimum degree `≥ 2` forces at least `n`. The core of a
connected graph is connected, so restricting to the connected case costs nothing here. -/

/-- **A connected graph of minimum degree `≥ 2` contains a cycle.** Classical; the shape Rubin's
argument needs at its first step. -/
theorem exists_isCycle_of_two_le_degree (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  by_contra hno
  push_neg at hno
  have hacyc : G.IsAcyclic := fun v c hc => hno v c hc
  have htree : G.IsTree := ⟨hconn, hacyc⟩
  have hcard : G.edgeFinset.card + 1 = Fintype.card V := htree.card_edgeFinset
  have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hle : 2 * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc 2 * Fintype.card V = ∑ _v : V, 2 := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ => hdeg v
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
  omega

/-- **A shortest cycle exists.** Well-ordering on lengths, given `exists_isCycle_of_two_le_degree`.
Rubin names this cycle `C₁`; minimality is used in his case analysis. -/
theorem exists_shortest_isCycle (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      ∀ (w : V) (d : G.Walk w w), d.IsCycle → c.length ≤ d.length := by
  classical
  obtain ⟨v₀, c₀, hc₀⟩ := exists_isCycle_of_two_le_degree hconn hdeg
  -- the set of lengths of cycles is a nonempty set of naturals, so it has a least element
  set S : Set ℕ := {n | ∃ (w : V) (d : G.Walk w w), d.IsCycle ∧ d.length = n} with hS
  have hne : S.Nonempty := ⟨c₀.length, v₀, c₀, hc₀, rfl⟩
  obtain ⟨w, d, hd, hdlen⟩ : sInf S ∈ S := Nat.sInf_mem hne
  refine ⟨w, d, hd, fun w' d' hd' => ?_⟩
  have : sInf S ≤ d'.length := Nat.sInf_le ⟨w', d', hd', rfl⟩
  omega

/-! ### Rubin's types 2 and 3, from Mathlib cycles

Two even cycles meeting in at most one vertex are **not** enough on their own — two *disjoint* even
cycles are `2`-choosable, since each is and colourings of a disjoint union are independent. Rubin's
types 2 and 3 therefore come with a connecting path (type 2) or a shared vertex (type 3, the
degenerate case of the path having length `0`). `ListColoring.not_choosable_two_of_dumbbell` covers
both. -/

/-- **Rubin's types 2 and 3, stated over Mathlib's cycles.** Given two cycle walks joined by a path
which is internally disjoint from both, the graph is not `2`-choosable.

The disjointness hypotheses are exactly those of `ListColoring.not_choosable_two_of_dumbbell`,
transported along the `getVert` bridge; the length-`0` path gives Rubin's type 3. -/
theorem not_choosable_two_of_two_cycle_walks {v w : V} {c₁ : G.Walk v v} {c₂ : G.Walk w w}
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) {l : ℕ} (P : ℕ → V)
    (hP : ∀ j, j < l → G.Adj (P j) (P (j + 1)))
    (hP₀ : P 0 = c₁.getVert 0) (hPl : P l = c₂.getVert 0)
    (hPinj : Set.InjOn P (Set.Iic l))
    (hAP : ∀ i, i ≤ c₁.length - 1 → ∀ j, 1 ≤ j → j ≤ l → c₁.getVert i ≠ P j)
    (hAB : ∀ i, i ≤ c₁.length - 1 → ∀ k, 1 ≤ k → k ≤ c₂.length - 1 →
      c₁.getVert i ≠ c₂.getVert k)
    (hPB : ∀ j, j ≤ l → ∀ k, 1 ≤ k → k ≤ c₂.length - 1 → P j ≠ c₂.getVert k) :
    ¬ G.Choosable 2 :=
  not_choosable_two_of_dumbbell (two_le_cycleWalk_bound hc₁) (two_le_cycleWalk_bound hc₂)
    c₁.getVert P c₂.getVert
    (fun _ hi => cycleWalk_adj c₁ hi) (cycleWalk_closes hc₁)
    hP (fun _ hk => cycleWalk_adj c₂ hk) (cycleWalk_closes hc₂)
    hP₀ hPl (cycleWalk_injOn hc₁) hPinj (cycleWalk_injOn hc₂) hAP hAB hPB

/-! ### E2 — the connecting path

Rubin's step 4 reads, in full:

> Let `P₁` be a shortest path, edge disjoint from `C₁`, and connecting two distinct nodes of `C₁`.
> (This is now known to exist.)

The parenthesis is the whole of the work: "now known" refers back to his step 3, which has just
disposed of every graph having a cycle that meets `C₁` in at most one node. This section proves
that existence claim, and proves it in the generality the rest of Rubin's argument needs — his
step 5 applies the very same reasoning with `C₁` replaced by `C₁ ∪ P₁`, so the statement is given
for an arbitrary set `S` of vertices and an arbitrary set `F` of already-used edges rather than for
a cycle.

The argument: take a vertex `u ∈ S` carrying an edge outside `F` (one exists, by connectedness);
extend it to a **longest** path out of `u` whose interior avoids `S`. Either the far end of that
path has a neighbour in `S` other than `u` — and then the path, extended by that one edge, is the
connecting path — or every neighbour of the far end lies on the path already, and, minimum degree
`≥ 2` giving a neighbour other than the penultimate vertex, a cycle closes inside the path. That
cycle meets `S` only in `u`, which is what the hypothesis on cycles forbids.

**Numerically checked before it was proved**, as this project's method requires: over all 316,460
connected bipartite non-cycle graphs of minimum degree `≥ 2` on at most `8` vertices — testing
*every* shortest cycle of each, not one — there is no failure, and none either for the
`S = C₁ ∪ P₁` form that Rubin's step 5 uses. -/

/-- Along a walk from inside `S` to outside `S` there is an edge that crosses the boundary. The
finite pigeonhole behind `ListColoring.exists_incident_edge_notMem`; not mathematics. -/
theorem exists_boundary_adj {S : Set V} :
    ∀ {a b : V} (_ : G.Walk a b), a ∈ S → b ∉ S → ∃ x y, G.Adj x y ∧ x ∈ S ∧ y ∉ S := by
  intro a b p
  induction p with
  | nil => intro ha hb; exact absurd ha hb
  | @cons x y z h q ih =>
    intro hx hz
    by_cases hy : y ∈ S
    · exact ih hy hz
    · exact ⟨x, y, h, hx, hy⟩

/-- **Some vertex of `S` carries an edge outside `F`.** Rubin's "note that there must exist an edge
of `G` not in `C₁`" is the hypothesis `hedge`; this lemma moves that edge to the boundary of `S`,
which is where the search for a connecting path has to start.

If no vertex of `S` carried an edge outside `F` then, `F` having both ends of each of its edges in
`S`, no edge would leave `S` at all; connectedness would force `S` to be everything, and then every
edge of `G` would lie in `F`. -/
theorem exists_incident_edge_notMem {S : Set V} {F : Set (Sym2 V)}
    (hconn : G.Connected) (hFS : ∀ {x y : V}, s(x, y) ∈ F → x ∈ S)
    (hSne : ∃ a, a ∈ S) (hedge : ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ F) :
    ∃ u w : V, u ∈ S ∧ G.Adj u w ∧ s(u, w) ∉ F := by
  by_contra hno
  push Not at hno
  obtain ⟨x, y, hxy, hxyF⟩ := hedge
  obtain ⟨a, ha⟩ := hSne
  have hxS : x ∉ S := fun hx => hxyF (hno x y hx hxy)
  obtain ⟨p⟩ := hconn.preconnected a x
  obtain ⟨c, d, hcd, hc, hd⟩ := exists_boundary_adj (S := S) p ha hxS
  have hF : s(c, d) ∈ F := hno c d hc hcd
  exact hd (hFS (show s(d, c) ∈ F by rw [Sym2.eq_swap]; exact hF))

/-- **E2, Rubin's connecting path.** In a connected graph of minimum degree `≥ 2`, let `S` be a
nonempty set of vertices and `F` a set of edges with both ends in `S` — think of `S` and `F` as the
vertices and edges of the subgraph built so far, Rubin's `C₁` or his `C₁ ∪ P₁`. If some edge of `G`
lies outside `F`, and **no cycle of `G` meets `S` in at most one vertex**, then there is a path
joining two *distinct* vertices of `S` whose interior avoids `S` and whose edges avoid `F`.

This is the existence claim Rubin asserts parenthetically ("This is now known to exist") at step 4
of his proof of the classification of `2`-choosable graphs (A. L. Rubin, in P. Erdős, A. L. Rubin
and H. Taylor, *Choosability in graphs*, Proc. West Coast Conf. on Combinatorics, Graph Theory and
Computing (Arcata, California, 1979), Congr. Numer. **26**, Utilitas Math., Winnipeg, **1980**,
125–157, p. 132). It is not a new result; only its proof is written out here, Rubin having left it
to the reader.

Rubin says "shortest path"; minimality is not needed for existence and is not claimed here. Where
his later steps use it — a shortest such path is automatically internally disjoint from `S`, which
is the sixth conjunct below — the corresponding property is stated outright instead. -/
theorem exists_connecting_path {S : Set V} {F : Set (Sym2 V)}
    (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (hFS : ∀ {x y : V}, s(x, y) ∈ F → x ∈ S)
    (hSne : ∃ a, a ∈ S) (hedge : ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ F)
    (hcyc : ∀ (z : V) (d : G.Walk z z), d.IsCycle →
      ∃ x ∈ d.support, ∃ y ∈ d.support, x ∈ S ∧ y ∈ S ∧ x ≠ y) :
    ∃ (a b : V) (p : G.Walk a b), a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ p.IsPath ∧ 1 ≤ p.length ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ S) ∧ ∀ e ∈ p.edges, e ∉ F := by
  classical
  obtain ⟨u, w, huS, huw, huwF⟩ := exists_incident_edge_notMem hconn hFS hSne hedge
  by_cases hwS : w ∈ S
  · -- `u w` is a chord: a connecting path of length one
    refine ⟨u, w, huw.toWalk, huS, hwS, huw.ne, SimpleGraph.Walk.IsPath.of_adj huw, by simp,
      ?_, ?_⟩
    · intro x hx hxu hxw
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd rfl hxu
      · exact absurd rfl hxw
    · intro e he
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; exact huwF
  · -- the main case: take a longest path out of `u` whose interior avoids `S`
    set P : ℕ → Prop := fun n => ∃ (z : V) (p : G.Walk u z), p.IsPath ∧ p.length = n ∧
        ∀ x ∈ p.support, x ≠ u → x ∉ S with hPdef
    have hP1 : P 1 := by
      refine ⟨w, huw.toWalk, SimpleGraph.Walk.IsPath.of_adj huw, by simp, ?_⟩
      intro x hx hxu
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd rfl hxu
      · exact hwS
    have hbound : ∀ n, P n → n ≤ Fintype.card V := by
      rintro n ⟨z, p, hp, rfl, -⟩
      exact le_of_lt hp.length_lt
    have hcard1 : 1 ≤ Fintype.card V := hbound 1 hP1
    have hPN : P (Nat.findGreatest P (Fintype.card V)) := Nat.findGreatest_spec hcard1 hP1
    have hmax : ∀ n, P n → n ≤ Nat.findGreatest P (Fintype.card V) := fun n hn =>
      Nat.le_findGreatest (hbound n hn) hn
    have hN1 : 1 ≤ Nat.findGreatest P (Fintype.card V) := hmax 1 hP1
    obtain ⟨z, p, hp, hplen, hint⟩ := hPN
    have hzu : z ≠ u := by
      rintro rfl
      have hp0 : p.length = 0 :=
        SimpleGraph.Walk.length_eq_zero_iff.mpr (SimpleGraph.Walk.isPath_iff_nil.mp hp)
      omega
    have hzS : z ∉ S := hint z p.end_mem_support hzu
    -- every edge of the path avoids `F`: it has an end other than `u`, and that end avoids `S`
    have hpF : ∀ e ∈ p.edges, e ∉ F := by
      intro e
      induction e using Sym2.ind with
      | _ c d =>
        intro he hF
        have hcd : G.Adj c d := p.adj_of_mem_edges he
        have hc : c ∈ p.support := p.fst_mem_support_of_mem_edges he
        have hd : d ∈ p.support := p.snd_mem_support_of_mem_edges he
        have hcS : c ∈ S := hFS hF
        have hdS : d ∈ S := hFS (show s(d, c) ∈ F by rw [Sym2.eq_swap]; exact hF)
        have hcu : c = u := by by_contra h; exact hint c hc h hcS
        have hdu : d = u := by by_contra h; exact hint d hd h hdS
        exact hcd.ne (hcu.trans hdu.symm)
    by_cases hcase : ∃ y : V, G.Adj z y ∧ y ∈ S ∧ y ≠ u
    · -- the far end has a neighbour on `S` other than `u`: one more edge finishes the path
      obtain ⟨y, hzy, hyS, hyu⟩ := hcase
      have hynp : y ∉ p.support := fun hy => hint y hy hyu hyS
      refine ⟨u, y, p.concat hzy, huS, hyS, Ne.symm hyu, hp.concat hynp hzy, ?_, ?_, ?_⟩
      · simp
      · intro x hx hxu hxy
        rw [SimpleGraph.Walk.support_concat] at hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hint x hx hxu
        · exact absurd rfl hxy
      · intro e he
        rw [SimpleGraph.Walk.edges_concat] at he
        simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hpF e he
        · exact fun hF => hzS (hFS hF)
    · -- otherwise every neighbour of the far end is already on the path, and a cycle closes
      push Not at hcase
      exfalso
      have hnbr : ∀ y : V, G.Adj z y → y ∈ p.support := by
        intro y hzy
        by_cases hyS : y ∈ S
        · rw [hcase y hzy hyS]; exact p.start_mem_support
        · by_contra hy
          have hbig : P (Nat.findGreatest P (Fintype.card V) + 1) := by
            refine ⟨y, p.concat hzy, hp.concat hy hzy, by simp [hplen], ?_⟩
            intro x hx hxu
            rw [SimpleGraph.Walk.support_concat] at hx
            simp only [List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hint x hx hxu
            · exact hyS
          exact absurd (hmax _ hbig) (by omega)
      have hrp : p.reverse.IsPath := hp.reverse
      have hrnil : ¬ p.reverse.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length, SimpleGraph.Walk.length_reverse]
        omega
      have hzm : G.Adj z p.reverse.snd := p.reverse.adj_snd hrnil
      -- minimum degree `≥ 2` supplies a neighbour of the far end other than the previous vertex
      obtain ⟨y, hzy, hym⟩ : ∃ y, G.Adj z y ∧ y ≠ p.reverse.snd := by
        have h2 : 1 < (G.neighborFinset z).card := by
          rw [G.card_neighborFinset_eq_degree]; exact hdeg z
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
        rw [SimpleGraph.mem_neighborFinset] at ha hb
        by_cases hA : a = p.reverse.snd
        · exact ⟨b, hb, fun h => hab (hA.trans h.symm)⟩
        · exact ⟨a, ha, hA⟩
      have hyr : y ∈ p.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact hnbr y hzy
      have hsupp : z :: p.reverse.tail.support = p.reverse.support :=
        SimpleGraph.Walk.cons_support_tail hrnil
      have hyt : y ∈ p.reverse.tail.support := by
        rw [← hsupp] at hyr
        rcases List.mem_cons.mp hyr with h | h
        · exact absurd h hzy.ne'
        · exact h
      have hztail : z ∉ p.reverse.tail.support := by
        intro hz
        have hcp := hrp
        rw [← SimpleGraph.Walk.cons_tail_eq p.reverse hrnil,
          SimpleGraph.Walk.cons_isPath_iff] at hcp
        exact hcp.2 hz
      set t := p.reverse.tail.takeUntil y hyt with ht
      have htp : t.IsPath := hrp.tail.takeUntil hyt
      have htsupp : ∀ x ∈ t.support, x ∈ p.reverse.tail.support := fun x hx =>
        SimpleGraph.Walk.support_takeUntil_subset_support _ hyt hx
      have hQp : (SimpleGraph.Walk.cons hzm t).IsPath := by
        rw [SimpleGraph.Walk.cons_isPath_iff]
        exact ⟨htp, fun hz => hztail (htsupp z hz)⟩
      have hQe : s(z, y) ∉ (SimpleGraph.Walk.cons hzm t).reverse.edges := by
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse,
          SimpleGraph.Walk.edges_cons, List.mem_cons]
        push Not
        refine ⟨?_, ?_⟩
        · intro h
          rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact hym h2
          · exact hzm.ne h1
        · intro h
          exact hztail (htsupp z (t.fst_mem_support_of_mem_edges h))
      have hcycle : (SimpleGraph.Walk.cons hzy (SimpleGraph.Walk.cons hzm t).reverse).IsCycle := by
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        exact ⟨hQp.reverse, hQe⟩
      obtain ⟨x1, hx1, x2, hx2, hx1S, hx2S, hne⟩ := hcyc z _ hcycle
      have hsub : ∀ x ∈ (SimpleGraph.Walk.cons hzy
          (SimpleGraph.Walk.cons hzm t).reverse).support, x ∈ p.support := by
        intro x hx
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact p.end_mem_support
        · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
            SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact p.end_mem_support
          · have h2 : x ∈ p.reverse.support := hsupp ▸ List.mem_cons_of_mem z (htsupp x hx)
            rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h2
            exact h2
      have e1 : x1 = u := by
        by_contra h; exact hint x1 (hsub x1 hx1) h hx1S
      have e2 : x2 = u := by
        by_contra h; exact hint x2 (hsub x2 hx2) h hx2S
      exact hne (e1.trans e2.symm)

/-- **E2 in the shape Rubin states it**: for a cycle `C₁` of a connected graph of minimum degree
`≥ 2`, if some edge of `G` is not an edge of `C₁` and no cycle of `G` meets `C₁` in at most one
vertex, then some path joins two distinct vertices of `C₁`, avoids `C₁` in its interior, and is
edge-disjoint from `C₁`.

The specialization of `ListColoring.exists_connecting_path` to `S` the vertices and `F` the edges of
`C₁`; Rubin's step 5 uses the general form instead, with `C₁ ∪ P₁` in place of `C₁`. -/
theorem exists_connecting_path_of_cycle {v : V} {c : G.Walk v v}
    (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (hedge : ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ c.edges)
    (hcyc : ∀ (z : V) (d : G.Walk z z), d.IsCycle →
      ∃ x ∈ d.support, ∃ y ∈ d.support, x ∈ c.support ∧ y ∈ c.support ∧ x ≠ y) :
    ∃ (a b : V) (p : G.Walk a b), a ∈ c.support ∧ b ∈ c.support ∧ a ≠ b ∧ p.IsPath ∧
      1 ≤ p.length ∧ (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support) ∧
      ∀ e ∈ p.edges, e ∉ c.edges :=
  exists_connecting_path (S := {x | x ∈ c.support}) (F := {e | e ∈ c.edges}) hconn hdeg
    (fun {_ _} h => c.fst_mem_support_of_mem_edges h) ⟨v, c.start_mem_support⟩ hedge hcyc

/-! ### Rubin's step 3, and the connecting path with its hypothesis discharged

Rubin's step 3 reads:

> If there is a cycle `C₂` having at most one node in common with `C₁`, then we will be in case
> (2.) or (3.), and be done.

The two cases are one theorem here (`ListColoring.not_choosable_two_of_dumbbell`, whose length-`0`
path is the shared-vertex case), so all that is needed is to produce the connecting path from
connectedness and to move the three walks into index form. The path is taken **shortest among all
paths joining the two cycles**; minimality is what makes its interior avoid both cycles, which is
what the dumbbell asks for.

The point of proving this here is that it converts the hypothesis of `exists_connecting_path` — "no
cycle meets `S` in at most one vertex" — into the hypothesis Rubin's proof actually has at that
point, namely that `G` is `2`-choosable. That composite is
`ListColoring.exists_connecting_path_of_choosable`, and it is the form his steps 4 and 5 both use.
-/

/-- **Rubin's step 3.** Two cycles of a connected graph meeting in at most one vertex make it not
`2`-choosable — his types 2 (node-disjoint cycles joined by a path) and 3 (cycles sharing one
node), which `ListColoring.not_choosable_two_of_dumbbell` covers together.

Due to A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West
Coast Conf. on Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congr. Numer.
**26**, Utilitas Math., Winnipeg, **1980**, 125–157, p. 132. The connecting path Rubin leaves
implicit is produced here as a shortest path between the two cycles, which is why its interior
misses both. -/
theorem not_choosable_two_of_cycles_meet_le_one {v z : V} {c₁ : G.Walk v v} {c₂ : G.Walk z z}
    (hconn : G.Connected) (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (hmeet : ∀ x y : V, x ∈ c₁.support → y ∈ c₁.support → x ∈ c₂.support → y ∈ c₂.support →
      x = y) :
    ¬ G.Choosable 2 := by
  classical
  set Q : ℕ → Prop := fun n => ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ a ∈ c₁.support ∧
      b ∈ c₂.support ∧ p.length = n with hQdef
  have hQ : ∃ n, Q n := by
    obtain ⟨wlk⟩ := hconn.preconnected v z
    exact ⟨wlk.bypass.length, v, z, wlk.bypass, wlk.bypass_isPath, c₁.start_mem_support,
      c₂.start_mem_support, rfl⟩
  obtain ⟨a, b, p, hp, ha, hb, hplen⟩ := Nat.find_spec hQ
  have hmin : ∀ n, Q n → Nat.find hQ ≤ n := fun n hn => Nat.find_min' hQ hn
  -- the interior of a shortest such path meets neither cycle
  have hF1 : ∀ x ∈ p.support, x ∈ c₁.support → x = a := by
    intro x hx hx1
    by_contra hxa
    have hlt : (p.dropUntil x hx).length < p.length :=
      SimpleGraph.Walk.length_dropUntil_lt_length hx hxa
    have hq : Q (p.dropUntil x hx).length := ⟨x, b, p.dropUntil x hx, hp.dropUntil hx, hx1, hb, rfl⟩
    have := hmin _ hq
    omega
  have hF2 : ∀ x ∈ p.support, x ∈ c₂.support → x = b := by
    intro x hx hx2
    by_contra hxb
    have hlt : (p.takeUntil x hx).length < p.length :=
      SimpleGraph.Walk.length_takeUntil_lt_length hx hxb
    have hq : Q (p.takeUntil x hx).length := ⟨a, x, p.takeUntil x hx, hp.takeUntil hx, ha, hx2, rfl⟩
    have := hmin _ hq
    omega
  -- a vertex lying on both cycles forces the path to be a single point
  have hdisj : ∀ x : V, x ∈ c₁.support → x ∈ c₂.support → x = b := by
    intro x hx1 hx2
    have h0 : Q 0 := ⟨x, x, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, hx1, hx2, rfl⟩
    have hN0 : Nat.find hQ = 0 := Nat.le_zero.mp (hmin 0 h0)
    have hpl : p.length = 0 := by omega
    have hab : a = b := SimpleGraph.Walk.eq_of_length_eq_zero hpl
    exact hmeet x b hx1 (hab ▸ ha) hx2 hb
  -- rotate both cycles so that they are based at the ends of the path
  have hr₁ : (c₁.rotate a ha).IsCycle := hc₁.rotate ha
  have hr₂ : (c₂.rotate b hb).IsCycle := hc₂.rotate hb
  have hmem₁ : ∀ i : ℕ, (c₁.rotate a ha).getVert i ∈ c₁.support := by
    intro i
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c₁ a ha]
    exact SimpleGraph.Walk.getVert_mem_support _ i
  have hmem₂ : ∀ i : ℕ, (c₂.rotate b hb).getVert i ∈ c₂.support := by
    intro i
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c₂ b hb]
    exact SimpleGraph.Walk.getVert_mem_support _ i
  refine not_choosable_two_of_two_cycle_walks hr₁ hr₂ (l := p.length) p.getVert
    (fun j hj => p.adj_getVert_succ (by omega)) ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · rw [p.getVert_length]; simp
  · intro i hi j hj
    exact hp.getVert_injOn hi hj
  · -- no vertex of the first cycle is an interior or far vertex of the path
    intro i _ j hj1 hj2 heq
    have hj0 : p.getVert j ≠ a := by
      intro h
      have h1 : j ∈ {i : ℕ | i ≤ p.length} := by simpa using hj2
      have h2 : (0 : ℕ) ∈ {i : ℕ | i ≤ p.length} := by simp
      have h3 : p.getVert j = p.getVert 0 := by rw [h, p.getVert_zero]
      have := hp.getVert_injOn h1 h2 h3
      omega
    have hmem : p.getVert j ∈ c₁.support := by rw [← heq]; exact hmem₁ i
    exact hj0 (hF1 (p.getVert j) (p.getVert_mem_support j) hmem)
  · -- the two cycles are disjoint away from the far end of the path
    intro i _ k hk1 hk2 heq
    have hbk : (c₂.rotate b hb).getVert k ≠ b := by
      intro h
      have h0 : (c₂.rotate b hb).getVert 0 = b := (c₂.rotate b hb).getVert_zero
      have h1 : k ∈ Set.Iic ((c₂.rotate b hb).length - 1) := by simp only [Set.mem_Iic]; omega
      have h2 : (0 : ℕ) ∈ Set.Iic ((c₂.rotate b hb).length - 1) := by simp
      have := hr₂.getVert_injOn' h1 h2 (h.trans h0.symm)
      omega
    have hmem : (c₂.rotate b hb).getVert k ∈ c₁.support := by rw [← heq]; exact hmem₁ i
    exact hbk (hdisj _ hmem (hmem₂ k))
  · -- no vertex of the path is an interior vertex of the second cycle
    intro j hj k hk1 hk2 heq
    have hbk : (c₂.rotate b hb).getVert k ≠ b := by
      intro h
      have h0 : (c₂.rotate b hb).getVert 0 = b := (c₂.rotate b hb).getVert_zero
      have h1 : k ∈ Set.Iic ((c₂.rotate b hb).length - 1) := by simp only [Set.mem_Iic]; omega
      have h2 : (0 : ℕ) ∈ Set.Iic ((c₂.rotate b hb).length - 1) := by simp
      have := hr₂.getVert_injOn' h1 h2 (h.trans h0.symm)
      omega
    have hmem : p.getVert j ∈ c₂.support := by rw [heq]; exact hmem₂ k
    apply hbk
    rw [← heq]
    exact hF2 (p.getVert j) (p.getVert_mem_support j) hmem

/-- **E2 with its hypothesis discharged.** In a connected, `2`-choosable graph of minimum degree
`≥ 2`, if `S` contains the vertices of some cycle, `F` is a set of edges with both ends in `S`, and
some edge of `G` lies outside `F`, then there is a path joining two distinct vertices of `S` whose
interior avoids `S` and whose edges avoid `F`.

This is the form Rubin's steps 4 and 5 use — step 4 with `S` the vertices of `C₁`, step 5 with `S`
the vertices of `C₁ ∪ P₁` — because at that point in his argument the hypothesis available is that
`G` is `2`-choosable, his step 3 having already dealt with a cycle meeting `C₁` in at most one
node. Combining `ListColoring.exists_connecting_path` with
`ListColoring.not_choosable_two_of_cycles_meet_le_one` is what turns one into the other; note that a
cycle meeting `S` in at most one vertex meets the smaller `C₁` in at most one vertex too, which is
why the same cycle hypothesis serves both applications. -/
theorem exists_connecting_path_of_choosable {S : Set V} {F : Set (Sym2 V)}
    (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v) (hch : G.Choosable 2)
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) (hcS : ∀ x ∈ c.support, x ∈ S)
    (hFS : ∀ {x y : V}, s(x, y) ∈ F → x ∈ S)
    (hedge : ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ F) :
    ∃ (a b : V) (p : G.Walk a b), a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ p.IsPath ∧ 1 ≤ p.length ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ S) ∧ ∀ e ∈ p.edges, e ∉ F := by
  refine exists_connecting_path hconn hdeg hFS ⟨v, hcS v c.start_mem_support⟩ hedge ?_
  intro z d hd
  by_contra hno
  push Not at hno
  exact not_choosable_two_of_cycles_meet_le_one hconn hc hd
    (fun x y hx1 hy1 hx2 hy2 => hno x hx2 y hy2 (hcS x hx1) (hcS y hy1)) hch

/-- **Rubin's `P₁` exists.** In a connected, `2`-choosable graph of minimum degree `≥ 2`, given a
cycle `C₁` and an edge of `G` outside it, some path joins two distinct vertices of `C₁`, avoids
`C₁` in its interior, and is edge-disjoint from `C₁`.

The specialization of `ListColoring.exists_connecting_path_of_choosable` to `S` and `F` the vertices
and edges of `C₁`; Rubin's step 5 uses the general form, with `C₁ ∪ P₁` in place of `C₁`. -/
theorem exists_connecting_path_of_cycle_of_choosable
    (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v) (hch : G.Choosable 2)
    {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    (hedge : ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ c.edges) :
    ∃ (a b : V) (p : G.Walk a b), a ∈ c.support ∧ b ∈ c.support ∧ a ≠ b ∧ p.IsPath ∧
      1 ≤ p.length ∧ (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support) ∧
      ∀ e ∈ p.edges, e ∉ c.edges :=
  exists_connecting_path_of_choosable (S := {x | x ∈ c.support}) (F := {e | e ∈ c.edges})
    hconn hdeg hch hc (fun _ h => h) (fun {_ _} h => c.fst_mem_support_of_mem_edges h) hedge

/-! ### What E4 still needs, and what the machine check says about it

`ListColoring.RubinTheorem` is **not** discharged; steps 4–6 of Rubin's proof and the assembly are
still open. Three observations from running his procedure exhaustively over all 316,460 connected
bipartite non-cycle graphs of minimum degree `≥ 2` on at most `8` vertices — every shortest cycle
`C₁`, every shortest admissible `P₁`, every shortest admissible `P₂` — are recorded here so they
are not rediscovered.

* **Cases (i) and (ii) of Rubin's six cannot occur.** Both describe a `P₂` producing a cycle that
  meets `C₁` in at most one node — none at all in case (i), exactly the node `a` in case (ii) —
  and step 3 has already disposed of every graph having such a cycle. Rubin says as much ("we are
  in case (2.) again"), but a formalization does not need to treat them: they contradict the
  hypothesis `ListColoring.exists_connecting_path_of_choosable` already carries. Neither case fires
  anywhere in the sweep, nor in a separate sweep over the configurations
  `C₁ ∪ P₁ ∪ P₂` built directly for `|P₁| ≤ 8`. Only cases (iii)–(vi) remain.
* **Case (v) needs `P₁` to be shortest.** With `P₂` joining the two branch vertices, the four arms
  have lengths `2, 2, |P₁|, |P₂|`; Rubin's "if `P₁` is of length `> 2` then we are in case (4.)"
  is right only because `P₂` is itself an admissible path for `C₁`, so `|P₁| ≤ |P₂|` and the arms
  `|P₁|, |P₂|` are then both `≠ 2`. Take `P₁` non-minimal and the claim fails: arms `2, 2, 4, 2`
  contain no bad three-arm theta. Alternatively, drop the sub-split — four arms is Rubin's type 5
  whatever their lengths, which `ListColoring.not_choosable_two_gtheta_of_four` covers.
* **Step 5's "`C₁` must be a 4-cycle" holds, and uses minimality of `C₁`.** If the theta
  `C₁ ∪ P₁` has shape `2, 2, ℓ` with the two `2`s the arcs of `C₁`, that is immediate; if instead
  an arc and `P₁` are the two `2`s, the `4`-cycle they form is at least as short as `C₁`, so `C₁`
  has length `4` anyway.

What is missing beyond steps 4–6 — and is not listed in `plan.md`'s E1–E4 — is the passage from
graph structure to `ListColoring.CoreIs`: that every connected graph *has* a core (a witness for
`ListColoring.CoreIs G H` with `H` of minimum degree `≥ 2`), and the two isomorphism constructions
`H ≃g closePath k` from `H` being connected and `2`-regular and `H ≃g theta m` from `H` being
`C₁ ∪ P₁` and nothing more. Steps 4–6 also need `ListColoring.Contains G (gtheta ks)` built from
walk data, which the abstract theta results (`ListColoring.choosable_two_gtheta_iff`,
`ListColoring.not_choosable_two_gtheta_of_four`) consume. -/

#print axioms ListColoring.exists_isCycle_of_two_le_degree
#print axioms ListColoring.exists_shortest_isCycle
#print axioms ListColoring.not_choosable_two_of_two_cycle_walks
#print axioms ListColoring.exists_boundary_adj
#print axioms ListColoring.exists_incident_edge_notMem
#print axioms ListColoring.exists_connecting_path
#print axioms ListColoring.exists_connecting_path_of_cycle
#print axioms ListColoring.not_choosable_two_of_cycles_meet_le_one
#print axioms ListColoring.exists_connecting_path_of_choosable
#print axioms ListColoring.exists_connecting_path_of_cycle_of_choosable

end ListColoring
