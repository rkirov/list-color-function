/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Cone
import ListColoring.Path

/-!
# Lemma 5 of Kirov–Naimi: pendant vertices and the core

The **core** of a graph is what is left after repeatedly deleting vertices of degree `1` until every
remaining vertex has degree at least `2`. Kirov–Naimi, Lemma 5, states that a connected graph is
enumeratively chromatic-choosable at `n` if and only if its core is. Since the core is reached by
finitely many pendant deletions, the whole content of the lemma is a *single pendant step*, proved
here in both directions.

The pendant step is an instance of coning off a clique: a pendant vertex is a new vertex joined to
the singleton `{v}`, and a singleton is always a clique. So the forward direction is exactly Lemma 1
(`SimpleGraph.ECCAt.coneOn`). The converse is the new content: given an `n`-list assignment `L` on
`G`, extend it to the cone by giving the *new* vertex the same list as its neighbour `v`. Every
coloring `f` of `G` from `L` then uses a color `f v` that the apex must avoid and which is present
in the apex list, so the apex has exactly `n - 1` free colors above every `f`, giving
`col(coneOn G {v}, M) = (n - 1) * col(G, L)` on the nose. Comparing this with
`col(coneOn G {v}, n) = (n - 1) * col(G, n)` and cancelling `n - 1` yields `G`'s enumerative
chromatic-choosability.

Cancelling `n - 1` needs `n ≠ 1`, and truncated subtraction needs `n ≠ 0`; but this is not a real
restriction, because *every* graph is enumeratively chromatic-choosable at `n` for `n ≤ 1`
(`SimpleGraph.ecc_of_le_one`). The equivalence is therefore proved for all `n`.

## Iterating: towers of pendant attachments

Formalizing "delete degree-one vertices until none are left" over an arbitrary vertex type forces
one to name the intermediate vertex types. We instead take the equivalent constructive form, which
is how Lemma 5 is actually used: `SimpleGraph.pendantTower G k d` is the graph obtained from `G` by
attaching `k` pendant vertices in succession, each one at an arbitrary vertex of the graph built so
far, and `SimpleGraph.ecc_pendantTower_iff` says that this graph is enumeratively
chromatic-choosable at `n` iff `G` is. Taking `G` to be the core of a graph `H` and the tower to be
the reversed sequence of pendant deletions leading from `H` to `G` gives Lemma 5.

## Main results

* `SimpleGraph.addPendant_eq_coneOn` : `G.addPendant v = coneOn G {v}`, a pendant vertex is a cone
  over a singleton
* `SimpleGraph.col_coneOn_singleton` : `col(coneOn G {v}, M) = ∑ f, |M none \ {f v}|`
* `SimpleGraph.colConst_coneOn_singleton` : `col(coneOn G {v}, n) = (n - 1) * col(G, n)`
* `SimpleGraph.col_coneOn_singleton_extend` : `col(coneOn G {v}, L⁺) = (n - 1) * col(G, L)` for the
  extension `L⁺` of `L` that repeats the list of `v` at the apex
* `SimpleGraph.ecc_of_le_one` : every graph is enumeratively chromatic-choosable at `n` for `n ≤ 1`
* `SimpleGraph.ecc_iff_forall_two_le` : consequently `SimpleGraph.ECC` only has content at `n ≥ 2`
* `SimpleGraph.ECCAt.addPendant` : the forward pendant step
* `SimpleGraph.ecc_of_ecc_coneOn_singleton` : the converse pendant step
* `SimpleGraph.ecc_coneOn_singleton_iff`, `SimpleGraph.ecc_addPendant_iff` : the two
  directions packaged as an `iff`, for every `n`
* `SimpleGraph.ecc_pendantTower_iff` : the iterated form, **Lemma 5**
-/

open Finset

universe u

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Transporting counts along an equality of graphs

`col` carries a `DecidableRel` instance argument, so an equality of graphs cannot simply be
rewritten inside it. These lemmas do the transport once and for all, comparing two graphs on the
same vertex type with unrelated decidability instances. -/

/-- The colorings of a graph depend only on its adjacency relation, not on the `DecidableRel`
instance used to define them. -/
theorem colorings_congr {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ a b, G.Adj a b ↔ G'.Adj a b) (L : ListAssignment V) :
    G.colorings L = G'.colorings L :=
  Finset.filter_congr fun _ _ =>
    ⟨fun hf _ _ hab => hf ((h _ _).mpr hab), fun hf _ _ hab => hf ((h _ _).mp hab)⟩

/-- `col` depends only on the adjacency relation. -/
theorem col_congr {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ a b, G.Adj a b ↔ G'.Adj a b) (L : ListAssignment V) : G.col L = G'.col L := by
  rw [col, col, colorings_congr h]

/-- `colConst` depends only on the adjacency relation. -/
theorem colConst_congr {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ a b, G.Adj a b ↔ G'.Adj a b) (n : ℕ) : G.colConst n = G'.colConst n :=
  col_congr h _

/-- Enumerative chromatic-choosability depends only on the adjacency relation. -/
theorem ecc_congr {G' : SimpleGraph V} [DecidableRel G'.Adj]
    (h : ∀ a b, G.Adj a b ↔ G'.Adj a b) (n : ℕ) : G.ECCAt n ↔ G'.ECCAt n := by
  unfold ECCAt
  simp_rw [colConst_congr h, col_congr h]

/-! ### A pendant vertex is a cone over a singleton -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **A pendant vertex is a cone over a singleton.** Attaching a new vertex to `v` alone is the
same as coning off the (necessarily complete) subgraph `{v}`. -/
theorem addPendant_eq_coneOn (v : V) : G.addPendant v = coneOn G {v} := by
  ext a b
  cases a <;> cases b <;>
    simp [addPendant, addPendantAdj, coneOn, coneAdj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A singleton is a clique, in the `Finset`-coerced form required by `ListColoring.Cone`. -/
theorem isClique_coe_singleton (v : V) : G.IsClique ((({v} : Finset V)) : Set V) := by
  rw [Finset.coe_singleton]
  exact isClique_singleton v

/-! ### The exact pendant count -/

/-- **The cone over a singleton.** Specializing `col_coneOn` to `K = {v}`: the apex may take any
color of its own list except the one used at `v`. -/
theorem col_coneOn_singleton (v : V) (M : ListAssignment (Option V)) :
    (coneOn G {v}).col M = ∑ f ∈ G.colorings (M ∘ some), (M none \ {f v}).card := by
  rw [col_coneOn]
  exact Finset.sum_congr rfl fun f _ => by rw [Finset.image_singleton]

/-- **Constant lists.** Attaching a pendant vertex multiplies the number of colorings from
the constant list of size `n` by exactly `n - 1`. -/
theorem colConst_coneOn_singleton (v : V) (n : ℕ) :
    (coneOn G {v}).colConst n = (n - 1) * G.colConst n := by
  rw [colConst_coneOn (isClique_coe_singleton v), Finset.card_singleton]

/-- The extension of a list assignment `L` on `V` to the cone that gives the apex the *same list as
its neighbour* `v`. This is the list assignment witnessing the converse pendant step. -/
def extendList (L : ListAssignment V) (v : V) : ListAssignment (Option V) :=
  fun o => o.elim (L v) L

omit [Fintype V] [DecidableEq V] in
@[simp] lemma extendList_none (L : ListAssignment V) (v : V) : extendList L v none = L v := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma extendList_some (L : ListAssignment V) (v : V) (w : V) :
    extendList L v (some w) = L w := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma extendList_comp_some (L : ListAssignment V) (v : V) :
    extendList L v ∘ some = L := rfl

omit [Fintype V] [DecidableEq V] in
/-- Extending an `n`-list assignment gives an `n`-list assignment. -/
theorem isNListAssignment_extendList {L : ListAssignment V} {n : ℕ} (hL : IsNListAssignment L n)
    (v : V) : IsNListAssignment (extendList L v) n := by
  rintro (_ | w)
  · exact hL v
  · exact hL w

/-- **The key construction.** If the apex is given the same list as its neighbour `v`, then
above *every* coloring `f` of `G` the apex has exactly `n - 1` free colors, because the forbidden
color `f v` is one of its own. Hence the cone count is exactly `(n - 1) * col(G, L)` — an equality,
where a general `n`-list assignment on the cone only gives an inequality. -/
theorem col_coneOn_singleton_extend {L : ListAssignment V} {n : ℕ} (hL : IsNListAssignment L n)
    (v : V) : (coneOn G {v}).col (extendList L v) = (n - 1) * G.col L := by
  rw [col_coneOn_singleton, extendList_comp_some]
  have key : ∀ f ∈ G.colorings L, (extendList L v none \ {f v}).card = n - 1 := by
    intro f hf
    rw [extendList_none, Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem (mem_list_of_mem_colorings hf v), hL v]
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ### Every graph is enumeratively chromatic-choosable at `n` for `n ≤ 1`

This removes the hypothesis `2 ≤ n` from the converse pendant step: for `n ≤ 1` the conclusion
holds outright. -/

/-- For `n ≤ 1` there is at most one coloring from the constant list, since there is at most one
function into a set with at most one element. -/
theorem colConst_le_one_of_le_one {n : ℕ} (hn : n ≤ 1) : G.colConst n ≤ 1 := by
  have h1 : G.colConst n ≤ (Fintype.piFinset (constList V n)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Fintype.card_piFinset] at h1
  have h2 : ∏ v : V, (constList V n v).card = n ^ (Finset.univ : Finset V).card := by
    simp [constList, Finset.prod_const]
  rw [h2] at h1
  calc G.colConst n ≤ n ^ (Finset.univ : Finset V).card := h1
    _ ≤ 1 ^ (Finset.univ : Finset V).card := Nat.pow_le_pow_left hn _
    _ = 1 := one_pow _

/-- **Every graph is enumeratively chromatic-choosable at `n` for `n ≤ 1`.** For `n = 0` there is
a coloring from the constant list only when `V` is empty, and for `n = 1` only when `G` has no
edges; in both cases every `n`-list assignment admits a coloring as well, and the constant count
is at most one. -/
theorem ecc_of_le_one {n : ℕ} (hn : n ≤ 1) : G.ECCAt n := by
  intro L hL
  rcases Nat.eq_zero_or_pos (G.colConst n) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  -- a coloring from the constant list exists; with `n ≤ 1` it is constantly `0`
  obtain ⟨f, hf⟩ := col_pos_iff.mp hpos
  have hf0 : ∀ v, f v = 0 := by
    intro v
    have : f v < n := Finset.mem_range.mp (mem_list_of_mem_colorings hf v)
    omega
  -- hence `G` has no edges at all
  have hno : ∀ a b, ¬ G.Adj a b := fun a b hab =>
    isProperColoring_of_mem_colorings hf hab ((hf0 a).trans (hf0 b).symm)
  -- every list of `L` is nonempty, so picking any color gives a coloring of `G` from `L`
  have hne : ∀ v, (L v).Nonempty := by
    intro v
    rw [← Finset.card_pos, hL v]
    have : f v < n := Finset.mem_range.mp (mem_list_of_mem_colorings hf v)
    omega
  have hpos' : 0 < G.col L := by
    rw [col_pos_iff]
    exact ⟨fun v => (hne v).choose,
      mem_colorings.mpr ⟨fun v => (hne v).choose_spec, fun a b hab => absurd hab (hno a b)⟩⟩
  have := colConst_le_one_of_le_one (G := G) hn
  omega

/-- **Only `n ≥ 2` has content.** `SimpleGraph.ECC` quantifies over every `n`, but the two smallest
values are free (`SimpleGraph.ecc_of_le_one`), so proving a graph enumeratively chromatic-choosable
never requires looking at `n ≤ 1`. -/
theorem ecc_iff_forall_two_le : G.ECC ↔ ∀ n, 2 ≤ n → G.ECCAt n := by
  refine ⟨fun h n _ => h.eccAt n, fun h n => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exact ecc_of_le_one (by omega)
  · exact h n hn

/-- Introduction rule for `SimpleGraph.ECC` from the cases that carry content. -/
theorem ecc_of_forall_two_le (h : ∀ n, 2 ≤ n → G.ECCAt n) : G.ECC :=
  ecc_iff_forall_two_le.mpr h

/-! ### Both directions of the pendant step -/

/-- **The forward pendant step.** If `G` is enumeratively chromatic-choosable at `n` then so is
`G` with a new pendant vertex attached at `v`. This is Lemma 1 of Kirov–Naimi applied to the
singleton clique `{v}`. -/
theorem ECCAt.addPendant {n : ℕ} (hG : G.ECCAt n) (v : V) :
    (SimpleGraph.coneOn G {v}).ECCAt n :=
  ECCAt.coneOn (isClique_coe_singleton v) hG

/-- The forward pendant step, phrased for `SimpleGraph.addPendant`. -/
theorem ECCAt.addPendant' {n : ℕ} (hG : G.ECCAt n) (v : V) :
    (G.addPendant v).ECCAt n :=
  (SimpleGraph.ecc_congr (fun _ _ => by rw [SimpleGraph.addPendant_eq_coneOn v]) n).mpr
    (ECCAt.addPendant hG v)

/-- **The converse pendant step** (the new content of Lemma 5). If attaching a pendant vertex at
`v` gives a graph enumeratively chromatic-choosable at `n`, then so is `G` itself.

Given an `n`-list assignment `L` on `G`, extend it to the cone by repeating the list of `v` at
the apex. Enumerative chromatic-choosability of the cone reads
`(n - 1) * col(G, n) ≤ (n - 1) * col(G, L)` by `colConst_coneOn_singleton` and
`col_coneOn_singleton_extend`, and `n - 1` cancels once `2 ≤ n`. For `n ≤ 1` the conclusion is
automatic (`ecc_of_le_one`), which is why `ecc_coneOn_singleton_iff` below needs no hypothesis on
`n`. -/
theorem ecc_of_ecc_coneOn_singleton {n : ℕ} (hn : 2 ≤ n) (v : V)
    (h : (coneOn G {v}).ECCAt n) : G.ECCAt n := by
  intro L hL
  have key := h (extendList L v) (isNListAssignment_extendList hL v)
  rw [colConst_coneOn_singleton, col_coneOn_singleton_extend hL] at key
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-- The converse pendant step, phrased for `SimpleGraph.addPendant`. -/
theorem ecc_of_ecc_addPendant {n : ℕ} (hn : 2 ≤ n) (v : V)
    (h : (G.addPendant v).ECCAt n) : G.ECCAt n :=
  ecc_of_ecc_coneOn_singleton hn v
    ((ecc_congr (fun a b => by rw [addPendant_eq_coneOn v]) n).mp h)

/-- **The pendant step, Kirov–Naimi Lemma 5 for a single vertex of degree one.** Attaching a
pendant vertex preserves and reflects enumerative chromatic-choosability at `n`.

No hypothesis on `n` is needed: for `n ≤ 1` both sides hold outright by
`ecc_of_le_one`. -/
theorem ecc_coneOn_singleton_iff (v : V) (n : ℕ) :
    (coneOn G {v}).ECCAt n ↔ G.ECCAt n := by
  refine ⟨fun h => ?_, fun h => ECCAt.addPendant h v⟩
  by_cases hn : 2 ≤ n
  · exact ecc_of_ecc_coneOn_singleton hn v h
  · exact ecc_of_le_one (by omega)

/-- The pendant step for `SimpleGraph.addPendant`. -/
theorem ecc_addPendant_iff (v : V) (n : ℕ) :
    (G.addPendant v).ECCAt n ↔ G.ECCAt n := by
  rw [ecc_congr (G' := coneOn G {v}) (fun _ _ => by rw [addPendant_eq_coneOn v]) n]
  exact ecc_coneOn_singleton_iff v n

/-! ### Iterating the pendant step

The core of a graph is reached from the graph by finitely many pendant deletions, so Lemma 5 is the
pendant step iterated. Read in the constructive direction, this says: attaching any finite sequence
of pendant vertices to `G` — each new vertex joined to an arbitrary vertex of the graph built so
far, possibly to an earlier new vertex — changes neither the enumerative chromatic-choosability at
`n` of `G` nor its failure. Applying this with `G` the core of a graph `H` and the tower the
sequence of pendant deletions leading from `H` down to `G` (reversed) gives Lemma 5 as stated in the
paper.

Since each attachment enlarges the vertex type by one element, the vertex type after `k` steps is
`Option`-iterated `k` times (`SimpleGraph.TowerV`), and the choice of attachment points is a nested
tuple of vertices, one from each intermediate type (`SimpleGraph.TowerData`). -/

section Tower

/-- The vertex type of `G` after `k` successive pendant attachments: `V` with `k` extra points. -/
def TowerV (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => Option (TowerV V k)

instance instDecidableEqTowerV {V : Type u} [DecidableEq V] : (k : ℕ) → DecidableEq (TowerV V k)
  | 0 => inferInstanceAs (DecidableEq V)
  | k + 1 =>
      letI := instDecidableEqTowerV (V := V) k
      inferInstanceAs (DecidableEq (Option (TowerV V k)))

instance instFintypeTowerV {V : Type u} [Fintype V] : (k : ℕ) → Fintype (TowerV V k)
  | 0 => inferInstanceAs (Fintype V)
  | k + 1 =>
      letI := instFintypeTowerV (V := V) k
      inferInstanceAs (Fintype (Option (TowerV V k)))

/-- The data specifying a tower of `k` pendant attachments: for each step, the already-existing
vertex at which the new pendant vertex is attached. -/
def TowerData (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => TowerData V k × TowerV V k

/-- **A tower of pendant attachments.** `pendantTower G k d` is the graph obtained from `G` by
attaching `k` pendant vertices one after another, the `i`-th of them at the vertex recorded in `d`
(which may itself be one of the earlier new vertices). -/
def pendantTower (G : SimpleGraph V) : (k : ℕ) → TowerData V k → SimpleGraph (TowerV V k)
  | 0, _ => G
  | k + 1, d => (pendantTower G k d.1).addPendant d.2

instance instDecidableRelPendantTower {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] : (k : ℕ) → (d : TowerData V k) → DecidableRel (pendantTower G k d).Adj
  | 0, _ => inferInstanceAs (DecidableRel G.Adj)
  | k + 1, d =>
      letI := instDecidableEqTowerV (V := V) k
      letI := instDecidableRelPendantTower (G := G) k d.1
      inferInstanceAs (DecidableRel ((pendantTower G k d.1).addPendant d.2).Adj)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma pendantTower_zero (d : TowerData V 0) : pendantTower G 0 d = G := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma pendantTower_succ (k : ℕ) (d : TowerData V (k + 1)) :
    pendantTower G (k + 1) d = (pendantTower G k d.1).addPendant d.2 := rfl

/-- **Kirov–Naimi, Lemma 5.** A graph built from `G` by any finite sequence of pendant attachments
is enumeratively chromatic-choosable at `n` if and only if `G` is.

Read from right to left this is the iterated forward step (Lemma 1); read from left to right it is
the iterated converse step. Taking `G` to be the core of a graph `H` — the result of repeatedly
deleting degree-one vertices, so that `H` is a pendant tower over `G` — gives the statement of the
paper: `H` is enumeratively chromatic-choosable at `n` iff its core is. -/
theorem ecc_pendantTower_iff (n : ℕ) :
    ∀ (k : ℕ) (d : TowerData V k), (pendantTower G k d).ECCAt n ↔ G.ECCAt n
  | 0, _ => Iff.rfl
  | k + 1, d =>
      letI := instDecidableEqTowerV (V := V) k
      letI := instFintypeTowerV (V := V) k
      letI := instDecidableRelPendantTower (G := G) k d.1
      (ecc_addPendant_iff (G := pendantTower G k d.1) d.2 n).trans
        (ecc_pendantTower_iff n k d.1)

end Tower

/-! ### Sanity checks -/

section Guards

open _root_.ListColoring

-- a path of length `2` is a path of length `1` with a pendant vertex attached at its endpoint
#guard (pathG 1).colConst 3 = 6
#guard (coneOn (pathG 1) {pathEnd 1}).colConst 3 = 2 * 6
#guard (pathG 2).colConst 3 = (coneOn (pathG 1) {pathEnd 1}).colConst 3
#guard (coneOn (pathG 2) {pathEnd 2}).colConst 4 = 3 * (pathG 2).colConst 4

-- the tower of two pendant attachments over a point is a path on three vertices: `3 * 2 * 2 = 12`
#guard (pendantTower (pathG 0) 2 ((PUnit.unit, pathEnd 0), pathEnd 1)).colConst 3 = 12

/-- The path of length `2` is literally a tower of two pendant attachments over the one-point
graph, so `ecc_pendantTower_iff` applies to it. -/
example : pendantTower (pathG 0) 2 ((PUnit.unit, pathEnd 0), pathEnd 1) = pathG 2 := rfl

end Guards

end SimpleGraph
