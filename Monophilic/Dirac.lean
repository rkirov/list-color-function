/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Chordal
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Chordal graphs, simplicial vertices, and Dirac's theorem

`Monophilic.Chordal` proves the Kostochka–Sidorenko theorem in its *ordering* form: a graph built
from nothing by repeatedly attaching a vertex to a clique is `n`-monophilic for every `n`. Nothing
there mentions chordality, because Mathlib has no notion of a chordal graph. This file supplies it.

## Main definitions

* `SimpleGraph.IsChordal` : every cycle of length at least `4` has a chord, phrased on top of
  Mathlib's `SimpleGraph.Walk.IsChordless`
* `SimpleGraph.IsSimplicialVertex` : the neighbourhood of the vertex is a clique

## Main results

* `SimpleGraph.isChordal_top` : complete graphs are chordal
* `SimpleGraph.not_isChordal_cycleGraph_four`, `SimpleGraph.not_isChordal_cycleGraph_five` : the
  four- and five-cycles are not
* `SimpleGraph.IsChordal.of_embedding`, `SimpleGraph.IsChordal.induce` : chordality is inherited by
  subgraphs induced on a set of vertices
* `SimpleGraph.IsChordal.coneOn` : coning off a clique of a chordal graph gives a chordal graph
* `SimpleGraph.isChordal_cliqueTower` : a simplicial clique tower builds a chordal graph
-/

open Finset

universe u

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Chordality and simplicial vertices -/

/-- **A chordal graph.** Every cycle of length at least `4` has a chord: an edge of the graph
joining two vertices of the cycle which is not itself an edge of the cycle.

The definition is phrased through Mathlib's `SimpleGraph.Walk.IsChordless`, which says that a walk
has no chord at all; so `IsChordal` asserts that no cycle of length `4` or more is chordless.
Triangles are excluded, as they must be: a triangle cannot have a chord. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ {u : V} (c : G.Walk u u), c.IsCycle → 4 ≤ c.length → ¬ c.IsChordless

/-- **A simplicial vertex** is one whose neighbourhood is a clique; equivalently, one whose closed
neighbourhood induces a complete subgraph. Deleting a simplicial vertex is the inverse of the cone
construction `SimpleGraph.coneOn`. -/
def IsSimplicialVertex (G : SimpleGraph V) (v : V) : Prop := G.IsClique (G.neighborSet v)

/-! ### Chords of a cycle

A chordless cycle is "locally a cycle": a vertex of the cycle can only be adjacent to its two
neighbours along the cycle. -/

/-- In a chordless cycle, the only vertices of the cycle adjacent to the basepoint are its two
neighbours along the cycle. -/
theorem Walk.IsChordless.eq_snd_or_penultimate {u x : V} {c : G.Walk u u} (hc : c.IsCycle)
    (hch : c.IsChordless) (hx : x ∈ c.support) (hadj : G.Adj u x) :
    x = c.snd ∨ x = c.penultimate := by
  have hmem : s(u, x) ∈ c.edges := hch.mem_edges c.start_mem_support hx hadj
  have hsub : c.toSubgraph.Adj u x :=
    Subgraph.mem_edgeSet.mp ((c.mem_edges_toSubgraph).mpr hmem)
  have hsub' : x ∈ c.toSubgraph.neighborSet u := hsub
  rw [hc.neighborSet_toSubgraph_endpoint] at hsub'
  simpa using hsub'

/-- **Complete graphs are chordal.** In a chordless cycle every vertex of the cycle is the
basepoint or one of its two cycle-neighbours, so a chordless cycle of a complete graph has at most
three vertices and hence length at most `3`. -/
theorem isChordal_top : (⊤ : SimpleGraph V).IsChordal := by
  classical
  intro u c hc hlen hch
  -- every vertex of the cycle lies in the three-element set `{u, c.snd, c.penultimate}`
  have hsub : ∀ x ∈ c.support.tail, x ∈ ({u, c.snd, c.penultimate} : Finset V) := by
    intro x hx
    have hxs : x ∈ c.support := List.mem_of_mem_tail hx
    by_cases hxu : x = u
    · simp [hxu]
    · rcases Walk.IsChordless.eq_snd_or_penultimate hc hch hxs
        (by simpa using fun h => hxu h.symm) with h | h <;> simp [h]
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hcard : c.support.tail.toFinset.card ≤ ({u, c.snd, c.penultimate} : Finset V).card :=
    Finset.card_le_card fun x hx => hsub x (List.mem_toFinset.mp hx)
  rw [List.toFinset_card_of_nodup hnodup, List.length_tail, c.length_support] at hcard
  have h3 : ({u, c.snd, c.penultimate} : Finset V).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  omega

/-- A graph with no vertices at all is chordal. -/
theorem isChordal_of_isEmpty [IsEmpty V] (G : SimpleGraph V) : G.IsChordal :=
  fun {u} _ _ _ _ => isEmptyElim u

/-- The empty graph is chordal: it has no cycles. -/
theorem isChordal_bot : (⊥ : SimpleGraph V).IsChordal := by
  intro u c hc _ _
  cases c with
  | nil => exact hc.ne_nil rfl
  | cons h _ => exact h.elim

/-! ### Chordality is inherited by induced subgraphs

Chordlessness of a walk is invariant under a graph embedding in both directions: a chord of the
image is an edge of the ambient graph between two image vertices, and an embedding reflects
adjacency. -/

section Embedding

variable {W : Type*} {G' : SimpleGraph W}

/-- A walk is chordless if and only if its image under a graph embedding is. -/
theorem Walk.isChordless_map_iff (f : G' ↪g G) {a b : W} (p : G'.Walk a b) :
    (p.map f.toHom).IsChordless ↔ p.IsChordless := by
  have hinj : Function.Injective f := f.injective
  rw [Walk.isChordless_iff_forall_mem_edges, Walk.isChordless_iff_forall_mem_edges]
  constructor
  · intro h x y hx hy hadj
    have hx' : f x ∈ (p.map f.toHom).support := by
      rw [Walk.support_map]; exact List.mem_map_of_mem hx
    have hy' : f y ∈ (p.map f.toHom).support := by
      rw [Walk.support_map]; exact List.mem_map_of_mem hy
    have := h hx' hy' (f.map_rel_iff.mpr hadj)
    rw [Walk.edges_map] at this
    obtain ⟨e, he, hee⟩ := List.mem_map.mp this
    have : e = s(x, y) := Sym2.map.injective hinj hee
    rwa [this] at he
  · intro h x y hx hy hadj
    rw [Walk.support_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    have := h hx' hy' (f.map_rel_iff.mp hadj)
    rw [Walk.edges_map]
    exact List.mem_map_of_mem this

/-- **Chordality passes to subgraphs presented by an embedding.** If `G` is chordal and `G'`
embeds into `G`, then `G'` is chordal. -/
theorem IsChordal.of_embedding (f : G' ↪g G) (h : G.IsChordal) : G'.IsChordal := by
  intro a c hc hlen hch
  refine h (c.map f.toHom) ((Walk.isCycle_map_iff_of_injective f.injective).mpr hc) ?_ ?_
  · rwa [Walk.length_map]
  · exact (Walk.isChordless_map_iff f c).mpr hch

/-- **Chordality is an isomorphism invariant.** -/
theorem IsChordal.of_iso (e : G' ≃g G) (h : G.IsChordal) : G'.IsChordal :=
  IsChordal.of_embedding e.toEmbedding h

/-- **Chordality passes to induced subgraphs.** -/
theorem IsChordal.induce (s : Set V) (h : G.IsChordal) : (G.induce s).IsChordal :=
  IsChordal.of_embedding (Embedding.induce s) h

end Embedding

/-! ### Coning off a clique preserves chordality

This is the easy direction of Dirac's theorem: the graphs built by a simplicial clique tower — the
graphs presented by a simplicial elimination ordering — are chordal. -/

section Cone

variable {K : Finset V}

/-- The vertices of the cone other than the apex, as a subtype, are the vertices of the base. -/
def someEquivNeNone (V : Type*) : V ≃ {x : Option V // x ≠ none} where
  toFun v := ⟨some v, by simp⟩
  invFun x := x.1.get (Option.isSome_iff_ne_none.mpr x.2)
  left_inv _ := rfl
  right_inv x := Subtype.ext (Option.some_get _)

/-- **The base of a cone is the subgraph induced on the non-apex vertices.** -/
def coneOnInduceIso (G : SimpleGraph V) (K : Finset V) :
    G ≃g (coneOn G K).induce {x : Option V | x ≠ none} where
  toEquiv := someEquivNeNone V
  map_rel_iff' := Iff.rfl

/-- Rotating a closed walk to a different basepoint preserves chordlessness: the supports and the
edge lists are rotations of one another. -/
theorem Walk.IsChordless.rotate [DecidableEq V] {v x : V} {c : G.Walk v v} (h : x ∈ c.support)
    (hch : c.IsChordless) : (c.rotate x h).IsChordless := by
  rw [Walk.isChordless_iff_forall_mem_edges] at hch ⊢
  intro a b ha hb hadj
  rw [(c.rotate_edges x h).perm.mem_iff]
  rw [Walk.mem_support_rotate_iff] at ha hb
  exact hch ha hb hadj

/-- **Coning off a clique preserves chordality.** If `G` is chordal and `K` is a clique of `G`,
then the graph obtained by adding a new vertex joined to `K` is chordal.

A cycle of the cone either avoids the apex — and then it already lives in `G` — or passes through
it, in which case its two neighbours along the cycle both lie in `K`, hence are adjacent; for a
cycle of length at least `4` that edge is a chord. -/
theorem IsChordal.coneOn (hG : G.IsChordal) (hK : G.IsClique (K : Set V)) :
    (coneOn G K).IsChordal := by
  classical
  intro o c hc hlen hch
  by_cases hnone : (none : Option V) ∈ c.support
  · -- the cycle passes through the apex; rotate it so that it starts there
    set d := c.rotate none hnone with hd
    have hc' : d.IsCycle := hc.rotate hnone
    have hlen' : 4 ≤ d.length := by rw [hd, Walk.length_rotate]; exact hlen
    have hch' : d.IsChordless := hch.rotate hnone
    -- the two cycle-neighbours of the apex lie in `K`
    have h1 : (SimpleGraph.coneOn G K).Adj none d.snd :=
      Subgraph.Adj.adj_sub (d.toSubgraph_adj_snd hc'.not_nil)
    have h2 : (SimpleGraph.coneOn G K).Adj d.penultimate none :=
      Subgraph.Adj.adj_sub (d.toSubgraph_adj_penultimate hc'.not_nil)
    have hsndK : ∃ a ∈ K, d.snd = some a := by
      cases hsd : d.snd with
      | none => rw [hsd] at h1; exact absurd h1 (coneOn_adj_none_none G K)
      | some a => rw [hsd] at h1; exact ⟨a, (coneOn_adj_none_some G K a).mp h1, rfl⟩
    have hpenK : ∃ b ∈ K, d.penultimate = some b := by
      cases hpd : d.penultimate with
      | none => rw [hpd] at h2; exact absurd h2 (coneOn_adj_none_none G K)
      | some b => rw [hpd] at h2; exact ⟨b, (coneOn_adj_some_none G K b).mp h2, rfl⟩
    obtain ⟨a, haK, hsa⟩ := hsndK
    obtain ⟨b, hbK, hpb⟩ := hpenK
    have hne : a ≠ b := by
      intro hab
      exact hc'.snd_ne_penultimate (by rw [hsa, hpb, hab])
    have hadj : (SimpleGraph.coneOn G K).Adj d.snd d.penultimate := by
      rw [hsa, hpb]
      exact hK haK hbK hne
    -- chordlessness forces that edge to be an edge of the cycle
    have hmem : s(d.snd, d.penultimate) ∈ d.edges :=
      hch'.mem_edges (d.getVert_mem_support 1) (d.getVert_mem_support (d.length - 1)) hadj
    have hadj' : d.toSubgraph.Adj d.snd d.penultimate :=
      Subgraph.mem_edgeSet.mp ((d.mem_edges_toSubgraph).mpr hmem)
    -- but the cycle-neighbours of `d.snd` are `d.getVert 0` and `d.getVert 2`
    have hnbr : d.penultimate ∈ d.toSubgraph.neighborSet (d.getVert 1) := hadj'
    rw [hc'.neighborSet_toSubgraph_internal (i := 1) (by omega) (by omega)] at hnbr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, show (1 : ℕ) - 1 = 0 from rfl,
      show (1 : ℕ) + 1 = 2 from rfl] at hnbr
    have hpen0 : d.penultimate ≠ d.getVert 0 := by
      rw [d.getVert_zero]
      exact h2.ne
    rcases hnbr with h | h
    · exact hpen0 h
    · -- `d.penultimate = d.getVert (d.length - 1)`, and `2 ≠ d.length - 1`
      have hpen : d.penultimate = d.getVert (d.length - 1) := rfl
      have h2mem : (2 : ℕ) ∈ {i : ℕ | 1 ≤ i ∧ i ≤ d.length} := by
        simp only [Set.mem_setOf_eq]; omega
      have hlmem : d.length - 1 ∈ {i : ℕ | 1 ≤ i ∧ i ≤ d.length} := by
        simp only [Set.mem_setOf_eq]; omega
      have := hc'.getVert_injOn h2mem hlmem (by rw [← h, hpen])
      omega
  · -- the cycle avoids the apex, so it lives in the base graph
    have hs : ∀ x ∈ c.support, x ∈ {x : Option V | x ≠ none} := by
      intro x hx
      simp only [Set.mem_setOf_eq, ne_eq]
      rintro rfl
      exact hnone hx
    have hbase : ((SimpleGraph.coneOn G K).induce {x : Option V | x ≠ none}).IsChordal :=
      IsChordal.of_iso (coneOnInduceIso G K).symm hG
    set f : ((SimpleGraph.coneOn G K).induce {x : Option V | x ≠ none}) ↪g
        (SimpleGraph.coneOn G K) := Embedding.induce {x : Option V | x ≠ none} with hf
    have hmap : (Walk.induce {x : Option V | x ≠ none} c hs).map f.toHom = c :=
      Walk.map_induce c hs
    refine hbase (Walk.induce {x : Option V | x ≠ none} c hs) ?_ ?_ ?_
    · refine (Walk.isCycle_map_iff_of_injective (f := f.toHom) f.injective).mp ?_
      rw [hmap]; exact hc
    · have hl := congrArg Walk.length hmap
      rw [Walk.length_map] at hl
      rw [hl]
      exact hlen
    · refine (Walk.isChordless_map_iff f _).mp ?_
      rw [hmap]; exact hch

end Cone

/-! ### The easy direction of Dirac's theorem

A graph presented by a simplicial elimination ordering — a simplicial clique tower over the empty
graph, in the language of `Monophilic.Chordal` — is chordal. -/

/-- **A simplicial clique tower builds a chordal graph.** -/
theorem isChordal_cliqueTower (G : SimpleGraph V) (hG : G.IsChordal) :
    ∀ (k : ℕ) (d : CliqueTowerData V k), CliqueTowerData.IsSimplicial G k d →
      (cliqueTower G k d).IsChordal
  | 0, _, _ => hG
  | k + 1, d, h => IsChordal.coneOn (isChordal_cliqueTower G hG k d.1 h.2) h.1

/-- **The easy direction of Dirac's theorem.** A graph built from nothing by successively attaching
a vertex to a clique of the graph built so far — that is, a graph presented by a simplicial
elimination ordering — is chordal. -/
theorem isChordal_cliqueTower_of_isEmpty {V : Type u} [IsEmpty V] (G : SimpleGraph V) (k : ℕ)
    (d : CliqueTowerData V k) (hd : CliqueTowerData.IsSimplicial G k d) :
    (cliqueTower G k d).IsChordal :=
  isChordal_cliqueTower G (isChordal_of_isEmpty G) k d hd

/-! ### Deleting a simplicial vertex

The inverse of `SimpleGraph.coneOn`: every graph is the cone, over the neighbourhood of any chosen
vertex `v`, of the graph obtained by deleting `v`. If `v` is simplicial that neighbourhood is a
clique, so Kirov–Naimi's Lemma 1 applies to the decomposition. -/

section Delete

variable [Fintype V] [DecidableEq V]

/-- `G` with the vertex `v` deleted: the subgraph induced on the vertices other than `v`. -/
abbrev deleteVertex (G : SimpleGraph V) (v : V) : SimpleGraph {x : V // x ≠ v} :=
  G.comap (Function.Embedding.subtype fun x => x ≠ v)

instance instDecidableRelDeleteVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (G.deleteVertex v).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a.1 b.1))

/-- The neighbours of `v`, viewed as a finset of vertices of `G.deleteVertex v`. Coning
`G.deleteVertex v` off along this finset reconstructs `G`. -/
def neighborsAway (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Finset {x : V // x ≠ v} :=
  Finset.univ.filter fun x => G.Adj v x.1

@[simp] lemma mem_neighborsAway (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    {x : {y : V // y ≠ v}} : x ∈ G.neighborsAway v ↔ G.Adj v x.1 := by
  simp [neighborsAway]

/-- **Every graph is a cone over the deletion of any one of its vertices.** -/
def coneOnDeleteIso (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G ≃g coneOn (G.deleteVertex v) (G.neighborsAway v) where
  toEquiv := (Equiv.optionSubtypeNe v).symm
  map_rel_iff' := by
    intro a b
    rcases eq_or_ne a v with rfl | ha
    · rcases eq_or_ne b a with rfl | hb
      · rw [Equiv.optionSubtypeNe_symm_self]
        simp
      · rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne hb]
        simp
    · rcases eq_or_ne b v with rfl | hb
      · rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne ha]
        simp only [coneOn_adj_some_none, mem_neighborsAway]
        exact adj_comm G b a
      · rw [Equiv.optionSubtypeNe_symm_of_ne ha, Equiv.optionSubtypeNe_symm_of_ne hb]
        exact Iff.rfl

/-- The neighbourhood of a simplicial vertex is a clique of the graph with that vertex deleted. -/
theorem isClique_neighborsAway (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hv : G.IsSimplicialVertex v) :
    (G.deleteVertex v).IsClique ((G.neighborsAway v : Finset {x : V // x ≠ v}) :
      Set {x : V // x ≠ v}) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, mem_neighborsAway] at hx hy
  exact hv hx hy fun h => hxy (Subtype.ext h)

omit [Fintype V] [DecidableEq V] in
/-- Deleting a vertex from a chordal graph leaves a chordal graph. -/
theorem IsChordal.deleteVertex {G : SimpleGraph V} (h : G.IsChordal) (v : V) :
    (G.deleteVertex v).IsChordal :=
  IsChordal.of_embedding (Embedding.comap (Function.Embedding.subtype fun x => x ≠ v) G) h

/-- Deleting a vertex removes exactly one vertex. -/
theorem card_deleteVertex (v : V) : Fintype.card {x : V // x ≠ v} + 1 = Fintype.card V := by
  have h := Fintype.card_congr (Equiv.optionSubtypeNe v)
  rwa [Fintype.card_option] at h

end Delete

/-! ### Towards Dirac's lemma: chordless paths inside a set of vertices

The classical proof that a chordal graph has a simplicial vertex runs through *minimal
separators*: a minimal `a`–`b` separator of a chordal graph is a clique, because two non-adjacent
vertices of the separator could be joined by a shortest path through each of the two sides, and the
two paths would close up into a long chordless cycle.

The technical engine of that argument is developed here: a walk of minimum length between two
vertices, among the walks confined to a prescribed set of vertices, is a chordless path. The point
is that a chord can always be short-circuited. -/

section ChordlessPath

/-- Consecutive vertices of a walk are joined by an edge of the walk. -/
theorem Walk.mem_edges_getVert {x y : V} (p : G.Walk x y) {i : ℕ} (hi : i < p.length) :
    s(p.getVert i, p.getVert (i + 1)) ∈ p.edges :=
  (p.mem_edges_toSubgraph).mp (Subgraph.mem_edgeSet.mpr (p.toSubgraph_adj_getVert hi))

/-- **Short-circuiting a chord.** If two vertices of a walk are joined by an edge of the graph
which is not an edge of the walk, replacing the stretch of the walk between them by that single
edge gives a strictly shorter walk with the same endpoints, using no new vertices. -/
theorem exists_shorter_of_chord {x y : V} (p : G.Walk x y) {i j : ℕ} (hij : i < j)
    (hj : j ≤ p.length) (hadj : G.Adj (p.getVert i) (p.getVert j))
    (hnot : s(p.getVert i, p.getVert j) ∉ p.edges) :
    ∃ q : G.Walk x y, q.length < p.length ∧ ∀ z ∈ q.support, z ∈ p.support := by
  -- the two vertices cannot be consecutive, else the edge would be an edge of the walk
  have hstep : i + 1 < j := by
    rcases Nat.lt_or_ge (i + 1) j with h | h
    · exact h
    · have hij' : j = i + 1 := by omega
      exact absurd (hij' ▸ p.mem_edges_getVert (i := i) (by omega)) (hij' ▸ hnot)
  refine ⟨(p.take i).append ((Walk.cons hadj Walk.nil).append (p.drop j)), ?_, ?_⟩
  · simp only [Walk.length_append, Walk.take_length, Walk.drop_length, Walk.length_cons,
      Walk.length_nil]
    omega
  · intro z hz
    rw [Walk.support_append] at hz
    rcases List.mem_append.mp hz with h | h
    · rw [Walk.support_take] at h
      exact List.mem_of_mem_take h
    · have h' := List.mem_of_mem_tail h
      rw [Walk.support_append] at h'
      rcases List.mem_append.mp h' with h'' | h''
      · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at h''
        rcases h'' with rfl | rfl
        · exact p.getVert_mem_support i
        · exact p.getVert_mem_support j
      · have h''' := List.mem_of_mem_tail h''
        rw [Walk.drop_support_eq_support_drop_min] at h'''
        exact List.mem_of_mem_drop h'''

/-- **A shortest confined walk is a chordless path.** If two vertices are joined by a walk all of
whose vertices lie in `W`, they are joined by a *chordless path* all of whose vertices lie in `W`,
and it is no longer than the walk one started from.

Minimality is what forces chordlessness: a chord could be short-circuited
(`SimpleGraph.exists_shorter_of_chord`), and repeated vertices could be bypassed. -/
theorem exists_isChordless_path {W : Set V} {x y : V} (p : G.Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ W) :
    ∃ q : G.Walk x y, (∀ z ∈ q.support, z ∈ W) ∧ q.IsPath ∧ q.IsChordless ∧
      q.length ≤ p.length := by
  classical
  have hex : ∃ n, ∃ q : G.Walk x y, (∀ z ∈ q.support, z ∈ W) ∧ q.length = n :=
    ⟨p.length, p, hp, rfl⟩
  obtain ⟨q₀, hq₀W, hq₀l⟩ := Nat.find_spec hex
  -- bypassing repeated vertices keeps the walk inside `W` and cannot lengthen it
  set q := q₀.bypass with hqdef
  have hqW : ∀ z ∈ q.support, z ∈ W := fun z hz => hq₀W z (q₀.support_bypass_subset hz)
  have hqle : q.length ≤ Nat.find hex := hq₀l ▸ q₀.length_bypass_le
  have hmin : Nat.find hex ≤ q.length := Nat.find_le ⟨q, hqW, rfl⟩
  have hqlen : q.length = Nat.find hex := le_antisymm hqle hmin
  refine ⟨q, hqW, q₀.bypass_isPath, ?_, ?_⟩
  · -- a chord could be short-circuited, contradicting minimality
    rw [Walk.isChordless_iff_forall_mem_edges]
    by_contra hcon
    push_neg at hcon
    obtain ⟨a, b, ha, hb, hadj, hnot⟩ := hcon
    obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp ha
    obtain ⟨j, hj, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hb
    have hne : i ≠ j := by
      intro h
      exact hadj.ne (by rw [← hi, ← hj, h])
    -- short-circuit, taking the two vertices in the order in which they occur
    have key : ∃ r : G.Walk x y, r.length < q.length ∧ ∀ z ∈ r.support, z ∈ q.support := by
      rcases Nat.lt_or_ge i j with h | h
      · exact exists_shorter_of_chord q h hjle (by rw [hi, hj]; exact hadj)
          (by rw [hi, hj]; exact hnot)
      · have h' : j < i := by omega
        refine exists_shorter_of_chord q h' hile (by rw [hi, hj]; exact hadj.symm) ?_
        rw [hi, hj, Sym2.eq_swap]
        exact hnot
    obtain ⟨r, hrlt, hrsub⟩ := key
    have : Nat.find hex ≤ r.length :=
      Nat.find_le ⟨r, fun z hz => hqW z (hrsub z hz), rfl⟩
    omega
  · exact le_trans hqle (Nat.find_le ⟨p, hp, rfl⟩)

/-- A chordless path of length at least two has non-adjacent endpoints: an edge between them would
be a chord. -/
theorem Walk.IsChordless.not_adj_of_two_le_length {x y : V} {p : G.Walk x y} (hp : p.IsPath)
    (hch : p.IsChordless) (hlen : 2 ≤ p.length) : ¬ G.Adj x y := by
  intro hadj
  have := hp.length_eq_one_of_mem_edges
    (hch.mem_edges p.start_mem_support p.end_mem_support hadj)
  omega

/-- The head of a path does not reappear in the rest of it. -/
theorem Walk.IsPath.start_notMem_support_tail {x y : V} {p : G.Walk x y} (hp : p.IsPath) :
    x ∉ p.support.tail := by
  have hnd := hp.support_nodup
  rw [p.support_eq_cons] at hnd
  exact (List.nodup_cons.mp hnd).1

/-- **Two chordless paths close up into a chordless cycle.** If two internally disjoint chordless
paths, each of length at least `2`, join the same pair of endpoints and no edge runs between their
interiors, then their union is a chordless cycle of length at least `4`; so no such configuration
exists in a chordal graph.

This is exactly the shape in which chordality enters the classical proof that a minimal separator
of a chordal graph is a clique: two non-adjacent vertices of the separator, joined by a shortest
path through each of the two components on either side of it. -/
theorem not_isChordal_of_chordless_paths {s t : V} {P Q : G.Walk s t}
    (hP : P.IsPath) (hQ : Q.IsPath) (hPch : P.IsChordless) (hQch : Q.IsChordless)
    (hPlen : 2 ≤ P.length) (hQlen : 2 ≤ Q.length)
    (hmeet : ∀ z ∈ P.support, z ∈ Q.support → z = s ∨ z = t)
    (hcross : ∀ a ∈ P.support, ∀ b ∈ Q.support, a ∉ Q.support → b ∉ P.support → ¬ G.Adj a b) :
    ¬ G.IsChordal := by
  intro hG
  have hQr : Q.reverse.IsPath := hQ.reverse
  have hmemQ : ∀ z, z ∈ Q.reverse.support ↔ z ∈ Q.support := by
    intro z; rw [Walk.support_reverse, List.mem_reverse]
  have hedgeQ : ∀ e, e ∈ Q.reverse.edges ↔ e ∈ Q.edges := by
    intro e; rw [Walk.edges_reverse, List.mem_reverse]
  -- the two paths meet only at their endpoints, so the closed walk is a cycle
  have hdisj : P.support.tail.Disjoint Q.reverse.support.tail := by
    intro z hz1 hz2
    have hz1' : z ∈ P.support := List.mem_of_mem_tail hz1
    have hz2' : z ∈ Q.support := (hmemQ z).mp (List.mem_of_mem_tail hz2)
    rcases hmeet z hz1' hz2' with rfl | rfl
    · exact hP.start_notMem_support_tail hz1
    · exact hQr.start_notMem_support_tail hz2
  have hcyc : (P.append Q.reverse).IsCycle :=
    hP.isCycle_append hQr hdisj (Or.inl (by omega))
  have hlen4 : 4 ≤ (P.append Q.reverse).length := by
    rw [Walk.length_append, Walk.length_reverse]; omega
  refine hG (P.append Q.reverse) hcyc hlen4 ?_
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro a b ha hb hadj
  rw [Walk.mem_support_append_iff] at ha hb
  rw [hmemQ] at ha hb
  rw [Walk.edges_append]
  by_cases hap : a ∈ P.support
  · by_cases hbp : b ∈ P.support
    · exact List.mem_append_left _ (hPch.mem_edges hap hbp hadj)
    · have hbq : b ∈ Q.support := hb.resolve_left hbp
      by_cases haq : a ∈ Q.support
      · exact List.mem_append_right _ ((hedgeQ _).mpr (hQch.mem_edges haq hbq hadj))
      · exact absurd hadj (hcross a hap b hbq haq hbp)
  · have haq : a ∈ Q.support := ha.resolve_left hap
    by_cases hbq : b ∈ Q.support
    · exact List.mem_append_right _ ((hedgeQ _).mpr (hQch.mem_edges haq hbq hadj))
    · have hbp : b ∈ P.support := hb.resolve_right hbq
      exact absurd hadj.symm (hcross b hbp a haq hbq hap)

end ChordlessPath

/-! ### The payoff: chordal graphs are `n`-monophilic

Kostochka and Sidorenko's theorem under its own name. What is needed to reach it from
`SimpleGraph.Monophilic.coneOn` is precisely **Dirac's lemma**: a chordal graph on a nonempty
finite vertex type has a simplicial vertex. Iterating that lemma peels the graph apart into a
simplicial elimination ordering, and each peeling step is Lemma 1.

Dirac's lemma is quarantined below as the explicit hypothesis
`SimpleGraph.HasSimplicialVertex`, in the same style as `monophilic_two_iff_of_rubin_hard` in
`Monophilic.Rubin`: the theorem that depends on it says so in its statement. -/

section Payoff

/-- **Dirac's lemma**, as a named hypothesis: every chordal graph on a nonempty finite vertex type
has a simplicial vertex.

This is the one graph-theoretic input that `SimpleGraph.monophilic_of_isChordal` below borrows. It
is a statement about graph structure alone and involves no colorings. -/
def HasSimplicialVertex : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), Nonempty V → G.IsChordal →
    ∃ v : V, G.IsSimplicialVertex v

/-- The induction behind the Kostochka–Sidorenko theorem, on the number of vertices: peel off a
simplicial vertex, recurse, and put it back with Kirov–Naimi's Lemma 1. -/
theorem monophilic_of_isChordal_aux (hD : HasSimplicialVertex.{u}) (n : ℕ) :
    ∀ (m : ℕ) {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = m → G.IsChordal → G.Monophilic n := by
  intro m
  induction m with
  | zero =>
      intro V _ _ G _ hcard _
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard
      exact monophilic_of_isEmpty G n
  | succ m ih =>
      intro V _ _ G _ hcard hch
      haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨v, hv⟩ := hD G inferInstance hch
      have hcard' : Fintype.card {x : V // x ≠ v} = m := by
        have := card_deleteVertex (V := V) v
        omega
      have hbase : (G.deleteVertex v).Monophilic n :=
        ih (G.deleteVertex v) hcard' (hch.deleteVertex v)
      exact (monophilic_iso (coneOnDeleteIso G v) n).mpr
        (Monophilic.coneOn (isClique_neighborsAway G hv) hbase)

/-- **The Kostochka–Sidorenko theorem, under its own name** — *modulo Dirac's lemma*. A chordal
graph is `n`-monophilic for every `n`.

The proof is a direct induction on the number of vertices through
`SimpleGraph.Monophilic.coneOn` (Kirov–Naimi's Lemma 1), rather than a detour through the
`SimpleGraph.cliqueTower` machinery of `Monophilic.Chordal`: given a simplicial vertex `v`, the
graph is the cone of `G.deleteVertex v` over the clique `G.neighborsAway v`, and `G.deleteVertex v`
is again chordal with one vertex fewer.

The hypothesis `hD` is Dirac's lemma; discharging it turns this into an unconditional theorem. -/
theorem monophilic_of_isChordal (hD : HasSimplicialVertex.{u}) {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) :
    G.Monophilic n :=
  monophilic_of_isChordal_aux hD n (Fintype.card V) G rfl hG

end Payoff

/-! ### Sanity checks on the definition

A definition of chordality that were accidentally vacuous would make everything above trivially
true. The checks below pin it down: complete graphs are chordal, and the four- and five-cycles are
not. The negative checks exhibit a concrete chordless cycle and verify chordlessness by
`decide`. -/

section Guards

/-- The triangle is chordal. -/
example : (⊤ : SimpleGraph (Fin 3)).IsChordal := isChordal_top

/-- `K₄` is chordal. -/
example : (⊤ : SimpleGraph (Fin 4)).IsChordal := isChordal_top

/-- The four-cycle `0 — 1 — 2 — 3 — 0`, written out as a closed walk. -/
private def c4 : (cycleGraph 4).Walk 0 0 :=
  .cons (show (cycleGraph 4).Adj 0 1 by decide)
    (.cons (show (cycleGraph 4).Adj 1 2 by decide)
      (.cons (show (cycleGraph 4).Adj 2 3 by decide)
        (.cons (show (cycleGraph 4).Adj 3 0 by decide) .nil)))

/-- The five-cycle `0 — 1 — 2 — 3 — 4 — 0`, written out as a closed walk. -/
private def c5 : (cycleGraph 5).Walk 0 0 :=
  .cons (show (cycleGraph 5).Adj 0 1 by decide)
    (.cons (show (cycleGraph 5).Adj 1 2 by decide)
      (.cons (show (cycleGraph 5).Adj 2 3 by decide)
        (.cons (show (cycleGraph 5).Adj 3 4 by decide)
          (.cons (show (cycleGraph 5).Adj 4 0 by decide) .nil))))

/-- **The four-cycle is not chordal.** -/
theorem not_isChordal_cycleGraph_four : ¬ (cycleGraph 4).IsChordal := by
  intro h
  refine h c4 ?_ (by decide) (Walk.isChordless_iff_forall_mem_edges.mpr (by decide))
  rw [Walk.isCycle_def]
  exact ⟨(Walk.isTrail_def _).mpr (by decide), by simp [c4], by decide⟩

/-- **The five-cycle is not chordal.** -/
theorem not_isChordal_cycleGraph_five : ¬ (cycleGraph 5).IsChordal := by
  intro h
  refine h c5 ?_ (by decide) (Walk.isChordless_iff_forall_mem_edges.mpr (by decide))
  rw [Walk.isCycle_def]
  exact ⟨(Walk.isTrail_def _).mpr (by decide), by simp [c5], by decide⟩

end Guards

end SimpleGraph
