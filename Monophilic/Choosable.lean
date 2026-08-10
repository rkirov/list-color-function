/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Core
import Monophilic.CycleRotate

/-!
# Infrastructure for choosability

`Monophilic.Basic` defines `SimpleGraph.Choosable G n` — every `n`-list assignment admits a proper
coloring — and relates it to `SimpleGraph.Colorable` and to `n`-monophilicity. This file develops
the structural theory of that predicate: how it transfers along isomorphisms, how it behaves under
adding or removing edges and vertices, and what it says about the two smallest graphs that matter
for `n = 2`.

The target is **Rubin's theorem**: a connected graph is `2`-choosable if and only if its core is a
single vertex, an even cycle, or the theta graph `θ_{2,2,2m}`. Theorem 2 of Kirov–Naimi currently
takes that classification as an explicit hypothesis
(`SimpleGraph.monophilic_two_iff_of_rubin` in `Monophilic.Theta`), and the results below are the
reusable pieces of its proof that do not depend on the classification itself:

* the "core" half of Rubin's statement — repeatedly deleting vertices of degree one changes
  nothing — is `SimpleGraph.choosable_pendantTower_iff`, proved here exactly as Kirov–Naimi's
  Lemma 5 is proved in `Monophilic.Core`: a pendant vertex is a cone over a singleton, and a cone
  over a singleton always has a free color left once `2 ≤ n`;
* two of the three graphs on Rubin's list are settled: a single vertex (indeed any edgeless graph)
  is `n`-choosable for `n ≥ 1`, and an even cycle is `2`-choosable — the latter is a corollary of
  Theorem 1 of Kirov–Naimi, since `col(C, 2) = 2 > 0` forces every `2`-list assignment to have at
  least one coloring;
* the sharpness of "even": a cycle on an odd number of vertices is not even `2`-colorable, hence
  not `2`-choosable.

## Main results

* `SimpleGraph.choosable_congr`, `SimpleGraph.choosable_iso` : choosability sees only the
  adjacency relation, and is an isomorphism invariant
* `SimpleGraph.Choosable.mono` : `G ≤ G' → G'.Choosable n → G.Choosable n`
* `SimpleGraph.Choosable.comap`, `SimpleGraph.Choosable.delNone` : choosability passes to a
  subgraph on a smaller vertex type, in particular to the graph with a vertex deleted
* `SimpleGraph.choosable_of_forall_not_adj` : an edgeless graph is `n`-choosable for `n ≥ 1`,
  and `SimpleGraph.choosable_of_subsingleton` : so is any graph on at most one vertex
* `SimpleGraph.choosable_coneOn_singleton_iff`, `SimpleGraph.choosable_addPendant_iff` : the
  pendant step, `(coneOn G {v}).Choosable n ↔ G.Choosable n` for `2 ≤ n`
* `SimpleGraph.choosable_pendantTower_iff` : the iterated pendant step — the core reduction
* `Monophilic.choosable_pathG` : every path is `n`-choosable for `n ≥ 2`, by the pendant step
* `Monophilic.choosable_two_closePath_of_odd` : a cycle on an even number of vertices is
  `2`-choosable
* `Monophilic.not_choosable_two_closePath_of_even` : a cycle on an odd number of vertices is not
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Transport

Choosability, like `col` itself, depends on the graph only through its adjacency relation, and is
invariant under renaming the vertices. -/

/-- Choosability depends only on the adjacency relation, not on the `DecidableRel` instance used to
count the colorings. Compare `SimpleGraph.monophilic_congr`. -/
theorem choosable_congr {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ a b, G.Adj a b ↔ G'.Adj a b) (n : ℕ) : G.Choosable n ↔ G'.Choosable n := by
  unfold Choosable
  simp_rw [col_congr h]

section Iso

variable {W : Type*} [Fintype W] [DecidableEq W] {G' : SimpleGraph W} [DecidableRel G'.Adj]

/-- **Choosability is an isomorphism invariant.** -/
theorem choosable_iso (e : G ≃g G') (n : ℕ) : G.Choosable n ↔ G'.Choosable n := by
  constructor
  · intro h M hM
    rw [← col_comp_iso e M]
    exact h _ (isNListAssignment_comp_iso e hM)
  · intro h L hL
    rw [← col_comp_iso e.symm L]
    exact h _ (isNListAssignment_comp_iso e.symm hL)

end Iso

/-! ### Monotonicity in the edges

Deleting edges can only make a graph easier to color. -/

/-- Every coloring of the larger graph is a coloring of the smaller one, from the same lists. -/
theorem colorings_subset_colorings_of_le {G' : SimpleGraph V} [DecidableRel G'.Adj] (h : G ≤ G')
    (L : ListAssignment V) : G'.colorings L ⊆ G.colorings L := by
  intro f hf
  rw [mem_colorings] at hf ⊢
  exact ⟨hf.1, fun _ _ hab => hf.2 (h hab)⟩

/-- Removing edges can only increase the number of list colorings. -/
theorem col_le_col_of_le {G' : SimpleGraph V} [DecidableRel G'.Adj] (h : G ≤ G')
    (L : ListAssignment V) : G'.col L ≤ G.col L :=
  card_le_card (colorings_subset_colorings_of_le h L)

/-- **Choosability passes to subgraphs on the same vertex type.** If `G ≤ G'` — same vertices,
fewer edges — and `G'` is `n`-choosable, then so is `G`. -/
theorem Choosable.mono {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj] {n : ℕ}
    (hG' : G'.Choosable n) (h : G ≤ G') : G.Choosable n := fun L hL =>
  lt_of_lt_of_le (hG' L hL) (col_le_col_of_le h L)

/-! ### Monotonicity in the vertices

A subgraph on a *smaller* vertex type is handled by the same idea plus one extension step: a list
assignment `L` on the small graph is extended to the big one by `Function.extend`, handing every
vertex outside the image the full palette `{0, …, n-1}`. A coloring of the big graph then restricts
along the injection to a coloring of the small one.

Stated for an arbitrary injective map preserving adjacency, this covers both edge deletion (take
the identity) and vertex deletion (take `some`, giving `SimpleGraph.Choosable.delNone`). -/

/-- **Choosability passes to subgraphs on a smaller vertex type.** If `f` embeds the vertices of
`G` into those of `G'` so that edges of `G` become edges of `G'`, and `G'` is `n`-choosable, then
so is `G`.

The list assignment on `G'` witnessing this gives `L v` to `f v` and the full palette to every
vertex outside the image, so it is again an `n`-list assignment. -/
theorem Choosable.comap {W : Type*} [Fintype W] [DecidableEq W] {G' : SimpleGraph W}
    [DecidableRel G'.Adj] {n : ℕ} (hG' : G'.Choosable n) {f : V → W} (hf : Function.Injective f)
    (hadj : ∀ a b, G.Adj a b → G'.Adj (f a) (f b)) : G.Choosable n := by
  intro L hL
  -- extend `L` along `f`, giving the full palette off the image
  set M : ListAssignment W := Function.extend f L (fun _ => range n) with hMdef
  have hMf : ∀ v, M (f v) = L v := fun v => hf.extend_apply L (fun _ => range n) v
  have hM : IsNListAssignment M n := by
    intro w
    by_cases h : ∃ v, f v = w
    · obtain ⟨v, rfl⟩ := h
      rw [hMf v]
      exact hL v
    · rw [hMdef, Function.extend_apply' _ _ _ h]
      exact card_range n
  obtain ⟨F, hF⟩ := col_pos_iff.mp (hG' M hM)
  rw [mem_colorings] at hF
  refine col_pos_iff.mpr
    ⟨F ∘ f, mem_colorings.mpr ⟨fun v => ?_, fun a b hab => hF.2 (hadj a b hab)⟩⟩
  have h := hF.1 (f v)
  rwa [hMf v] at h

/-- **Choosability passes to vertex-deleted subgraphs.** If `H` is a graph on `Option V` and `H` is
`n`-choosable, then so is the graph `H − none` on `V`. -/
theorem Choosable.delNone {H : SimpleGraph (Option V)} [DecidableRel H.Adj] {n : ℕ}
    (hH : H.Choosable n) : H.delNone.Choosable n :=
  hH.comap (Option.some_injective V) fun _ _ hab => hab

/-! ### Edgeless graphs

The first entry of Rubin's list of cores is a single vertex. Nothing is special about one vertex:
any graph without edges is `n`-choosable as soon as every list is nonempty. -/

/-- **An edgeless graph is `n`-choosable for every `n ≥ 1`**: choose any color from each list. -/
theorem choosable_of_forall_not_adj {n : ℕ} (hn : 1 ≤ n) (h : ∀ a b, ¬ G.Adj a b) :
    G.Choosable n := by
  intro L hL
  have hne : ∀ v, (L v).Nonempty := by
    intro v
    rw [← Finset.card_pos, hL v]
    exact hn
  exact col_pos_iff.mpr ⟨fun v => (hne v).choose,
    mem_colorings.mpr ⟨fun v => (hne v).choose_spec, fun a b hab => absurd hab (h a b)⟩⟩

/-- **`K₁` is `n`-choosable for `n ≥ 1`**, and more generally any graph on at most one vertex: a
simple graph has no loops, so there is nothing to violate. -/
theorem choosable_of_subsingleton [Subsingleton V] {n : ℕ} (hn : 1 ≤ n) : G.Choosable n :=
  choosable_of_forall_not_adj hn fun a b hab => hab.ne (Subsingleton.elim a b)

/-- The empty graph on any vertex type is `n`-choosable for `n ≥ 1`. -/
theorem choosable_bot {n : ℕ} (hn : 1 ≤ n) : (⊥ : SimpleGraph V).Choosable n :=
  choosable_of_forall_not_adj hn fun _ _ h => h

/-! ### The pendant step

A pendant vertex is a cone over a singleton (`SimpleGraph.addPendant_eq_coneOn`), so the two
directions below are the choosability analogue of Kirov–Naimi's Lemma 5, proved in
`Monophilic.Core` for monophilicity.

The forward direction — restrict a coloring of the cone — needs no hypothesis on `n`. The backward
direction needs `2 ≤ n`: the apex must avoid the single color used at its neighbour, and it has `n`
colors of its own to choose from, so `n - 1 ≥ 1` remain. For `n ≤ 1` the statement is genuinely
false: a single edge is not `1`-choosable, but a single vertex is. -/

/-- **The forward pendant step for choosability.** If attaching a pendant vertex at `v` gives an
`n`-choosable graph then `G` itself is `n`-choosable: extend a list assignment `L` on `G` by
repeating the list of `v` at the apex, and restrict a coloring of the cone back to `G`. -/
theorem choosable_of_choosable_coneOn_singleton {n : ℕ} (v : V)
    (h : (coneOn G {v}).Choosable n) : G.Choosable n := by
  intro L hL
  obtain ⟨F, hF⟩ := col_pos_iff.mp (h (extendList L v) (isNListAssignment_extendList hL v))
  exact col_pos_iff.mpr ⟨F ∘ some, by
    simpa only [extendList_comp_some] using comp_some_mem_colorings hF⟩

/-- **The backward pendant step for choosability.** For `2 ≤ n`, attaching a pendant vertex to an
`n`-choosable graph leaves it `n`-choosable: color `G` first, and then the apex — whose own list has
`n ≥ 2` colors, at most one of which is forbidden by its unique neighbour — still has a color
available. -/
theorem Choosable.coneOn_singleton {n : ℕ} (hn : 2 ≤ n) (hG : G.Choosable n) (v : V) :
    (SimpleGraph.coneOn G {v}).Choosable n := by
  intro M hM
  have h1 : 0 < G.col (M ∘ some) := hG (M ∘ some) fun w => hM (some w)
  have h2 : (n - ({v} : Finset V).card) * G.col (M ∘ some) ≤ (coneOn G {v}).col M :=
    mul_col_le_col_coneOn hM
  rw [Finset.card_singleton] at h2
  have h3 : 0 < (n - 1) * G.col (M ∘ some) := Nat.mul_pos (by omega) h1
  omega

/-- **The pendant step for choosability**, packaged as an `iff`: for `2 ≤ n`, coning off a single
vertex preserves and reflects `n`-choosability. -/
theorem choosable_coneOn_singleton_iff {n : ℕ} (hn : 2 ≤ n) (v : V) :
    (coneOn G {v}).Choosable n ↔ G.Choosable n :=
  ⟨choosable_of_choosable_coneOn_singleton v, fun h => h.coneOn_singleton hn v⟩

/-- The pendant step for `SimpleGraph.addPendant`. -/
theorem choosable_addPendant_iff {n : ℕ} (hn : 2 ≤ n) (v : V) :
    (G.addPendant v).Choosable n ↔ G.Choosable n := by
  rw [choosable_congr (G' := coneOn G {v}) (fun _ _ => by rw [addPendant_eq_coneOn v]) n]
  exact choosable_coneOn_singleton_iff hn v

/-! ### Towers of pendant attachments: the core reduction

Iterating the pendant step over the tower construction of `Monophilic.Core` gives the choosability
form of Kirov–Naimi's Lemma 5, which is the "core" half of Rubin's theorem: attaching any finite
sequence of pendant vertices to `G` — each new vertex joined to an arbitrary vertex of the graph
built so far — changes neither the `n`-choosability of `G` nor its failure. Reading `G` as the core
of a graph `H` and the tower as the reversed sequence of degree-one deletions leading from `H` to
`G` gives: `H` is `n`-choosable iff its core is. -/

/-- **The core reduction for choosability.** For `2 ≤ n`, a graph built from `G` by any finite
sequence of pendant attachments is `n`-choosable if and only if `G` is. This mirrors
`SimpleGraph.monophilic_pendantTower_iff`, and is the step of Rubin's theorem that reduces a
connected graph to its core. -/
theorem choosable_pendantTower_iff {n : ℕ} (hn : 2 ≤ n) :
    ∀ (k : ℕ) (d : TowerData V k), (pendantTower G k d).Choosable n ↔ G.Choosable n
  | 0, _ => Iff.rfl
  | k + 1, d =>
      letI := instDecidableEqTowerV (V := V) k
      letI := instFintypeTowerV (V := V) k
      letI := instDecidableRelPendantTower (G := G) k d.1
      (choosable_addPendant_iff (G := pendantTower G k d.1) hn d.2).trans
        (choosable_pendantTower_iff hn k d.1)

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-! ### Paths

A path is a tower of pendant attachments over a single vertex, which is exactly the situation the
pendant step covers. This is both a sanity check on `SimpleGraph.choosable_addPendant_iff` and the
first instance of the core reduction: a path collapses, one degree-one vertex at a time, to the
single-vertex graph at the head of Rubin's list. -/

/-- **Every path is `n`-choosable for `n ≥ 2`**, by induction along the pendant step: `pathG (k+1)`
is `pathG k` with one pendant vertex attached, and `pathG 0` is a single vertex. -/
theorem choosable_pathG {n : ℕ} (hn : 2 ≤ n) : ∀ k : ℕ, (pathG k).Choosable n
  | 0 =>
      letI : Subsingleton (PathV 0) := inferInstanceAs (Subsingleton Unit)
      choosable_of_subsingleton (by omega)
  | k + 1 =>
      (choosable_addPendant_iff (G := pathG k) hn (pathEnd k)).mpr (choosable_pathG hn k)

/-! ### Cycles

`closePath k` is the cycle on `k + 1` vertices (for `k ≥ 2`), so `Odd k` says that the cycle has an
**even** number of vertices. Both statements below are read off from the count `col(C, 2)`: it is
`2` for an even cycle and `0` for an odd one. -/

/-- **An even cycle is `2`-choosable.** `closePath k` has `k + 1` vertices, so `Odd k` says that
number is even.

This is a corollary of Theorem 1 of Kirov–Naimi (`Monophilic.monophilic_closePath_of_two_le`):
`2`-monophilicity says that the constant list assignment *minimizes* the number of colorings, and
that minimum is `col(C, 2) = 2` by `Monophilic.colConst_closePath_two_of_odd`. So every `2`-list
assignment admits at least two colorings, in particular at least one. -/
theorem choosable_two_closePath_of_odd {k : ℕ} (hk : Odd k) (hk2 : 2 ≤ k) :
    (closePath k).Choosable 2 := by
  intro L hL
  have h := monophilic_closePath_of_two_le (m := 0) hk2 L hL
  rw [colConst_closePath_two_of_odd hk] at h
  omega

/-- **`col(C, 2) = 0` for a cycle on an odd number of vertices.** `closePath k` has `k + 1`
vertices, so `Even k` says that number is odd; `2 ≤ k` excludes the degenerate `closePath 0`, a
single vertex, which does have `col = 2`.

At `n = 2` the recurrence of Lemma 3 alternates between `A_j = 1` and `A_j = 0`
(`Monophilic.pathA_pathB_zero_parity`), and `col(C, 2) = 2 · A_{k-1}` vanishes precisely when
`k - 1` is odd. -/
theorem colConst_closePath_two_of_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    (closePath k).colConst 2 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : ¬ Even j := Nat.even_add_one.mp hk
  have h := colConst_closePath_succ 0 j
  rw [(pathA_pathB_zero_parity j).1, if_neg hj] at h
  simpa only [zero_add, mul_zero] using h

/-- **A cycle on an odd number of vertices is not `2`-colorable.** -/
theorem not_colorable_two_closePath_of_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    ¬ (closePath k).Colorable 2 :=
  colConst_eq_zero_iff_not_colorable.mp (colConst_closePath_two_of_even hk hk2)

/-- **An odd cycle is not `2`-choosable.** Since `χ(G) ≤ χ_ℓ(G)`
(`SimpleGraph.colorable_of_choosable`), a graph that is not `2`-colorable cannot be `2`-choosable.
Together with `Monophilic.choosable_two_closePath_of_odd` this pins down exactly which cycles
belong to Rubin's list: the even ones. -/
theorem not_choosable_two_closePath_of_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    ¬ (closePath k).Choosable 2 := fun h =>
  not_colorable_two_closePath_of_even hk hk2 (colorable_of_choosable h)

/-- **A single vertex is `n`-choosable for `n ≥ 1`**, in the concrete form `closePath 0`: the first
entry of Rubin's list of `2`-choosable cores. -/
theorem choosable_closePath_zero {n : ℕ} (hn : 1 ≤ n) : (closePath 0).Choosable n :=
  letI : Subsingleton (PathV 0) := inferInstanceAs (Subsingleton Unit)
  choosable_of_subsingleton hn

end Monophilic

/-! ### Sanity checks -/

section Guards

open Monophilic SimpleGraph

-- `C₄` and `C₆` are `2`-choosable, `C₃` and `C₅` are not: the counts they come from.
#guard (closePath 3).colConst 2 = 2
#guard (closePath 5).colConst 2 = 2
#guard (closePath 2).colConst 2 = 0
#guard (closePath 4).colConst 2 = 0

-- the pendant step, numerically: attaching a pendant vertex multiplies `col(·, 2)` by `2 - 1 = 1`
#guard (pathG 3).colConst 2 = 2
#guard (coneOn (pathG 3) {pathEnd 3}).colConst 2 = (pathG 3).colConst 2

/-- The path of length `2` is literally a tower of two pendant attachments over the one-point
graph, so `SimpleGraph.choosable_pendantTower_iff` applies to it verbatim. -/
example {n : ℕ} (hn : 2 ≤ n) :
    (pendantTower (pathG 0) 2 ((PUnit.unit, pathEnd 0), pathEnd 1)).Choosable n ↔
      (pathG 0).Choosable n :=
  choosable_pendantTower_iff hn 2 _

end Guards

#print axioms SimpleGraph.choosable_congr
#print axioms SimpleGraph.choosable_iso
#print axioms SimpleGraph.Choosable.mono
#print axioms SimpleGraph.Choosable.comap
#print axioms SimpleGraph.Choosable.delNone
#print axioms SimpleGraph.choosable_of_forall_not_adj
#print axioms SimpleGraph.choosable_of_subsingleton
#print axioms SimpleGraph.choosable_bot
#print axioms SimpleGraph.choosable_of_choosable_coneOn_singleton
#print axioms SimpleGraph.Choosable.coneOn_singleton
#print axioms SimpleGraph.choosable_coneOn_singleton_iff
#print axioms SimpleGraph.choosable_addPendant_iff
#print axioms SimpleGraph.choosable_pendantTower_iff
#print axioms Monophilic.choosable_pathG
#print axioms Monophilic.choosable_two_closePath_of_odd
#print axioms Monophilic.colConst_closePath_two_of_even
#print axioms Monophilic.not_colorable_two_closePath_of_even
#print axioms Monophilic.not_choosable_two_closePath_of_even
#print axioms Monophilic.choosable_closePath_zero
