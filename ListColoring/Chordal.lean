/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Core

/-!
# The Kostochka–Sidorenko corollary: simplicial elimination orderings

Kirov–Naimi record, as a corollary of their Lemma 1, the theorem of Kostochka and Sidorenko that
**every chordal graph is enumeratively chromatic-choosable at `n` for every `n`**. The proof is an
induction along a *simplicial elimination ordering*: order the vertices `v₁, …, v_m` so that each
`v_i` is simplicial in the graph induced by `v₁, …, v_i`, i.e. its neighbours among the earlier
vertices form a clique. Reading the ordering backwards, the graph is built from the empty graph by
repeatedly adding a new vertex joined to a clique of the graph constructed so far — and each such
step preserves enumerative chromatic-choosability at `n` by Lemma 1 (`SimpleGraph.ECCAt.coneOn`).

This file formalizes exactly that: the *ordering* form of chordality. Dirac's theorem — a graph is
chordal (every cycle of length at least four has a chord) if and only if it admits a simplicial
elimination ordering — is what would connect the statement below to the word "chordal" as usually
defined. It is a purely structural graph-theoretic fact with no bearing on list colorings, and it is
**not part of this development**.

## The tower

As in `ListColoring.Core`, adding a vertex enlarges the vertex type by one point, so after `k` steps
the vertex type is `SimpleGraph.TowerV V k` (`V` with `k` extra points, reused verbatim from
`ListColoring.Core`) and the construction data is a nested tuple recording, at each stage, the set
of old vertices the new vertex is joined to (`SimpleGraph.CliqueTowerData`). This generalizes
`SimpleGraph.pendantTower`, where every attachment set is a singleton, to arbitrary attachment sets;
the hypothesis that each of them is a clique *in the graph existing at that stage* is
`SimpleGraph.CliqueTowerData.IsSimplicial`.

## Main results

* `SimpleGraph.CliqueTowerData` : the data of a tower of cone attachments
* `SimpleGraph.cliqueTower` : the graph built by such a tower
* `SimpleGraph.CliqueTowerData.IsSimplicial` : every attachment set is a clique at its stage
* `SimpleGraph.ecc_cliqueTower` : a simplicial tower over a graph enumeratively
  chromatic-choosable at `n` is again enumeratively chromatic-choosable at `n`
* `SimpleGraph.ecc_cliqueTower_of_isEmpty` : **the Kostochka–Sidorenko corollary**, in its
  simplicial-elimination-ordering form: a graph built by a simplicial tower over the empty graph is
  enumeratively chromatic-choosable at `n` for every `n`
* `SimpleGraph.ecc_pendantTower_of_cliqueTower` : a pendant tower is the special case in
  which every attachment set is a singleton
* `SimpleGraph.ecc_top_fin_of_cliqueTower` : complete graphs recovered from the corollary
-/

open Finset

universe u

namespace SimpleGraph

/-! ### Towers of cones over cliques -/

section Tower

variable {V : Type u}

/-- The data specifying a tower of `k` cone attachments over `V`: at each stage, the finset of
already-existing vertices that the new vertex is joined to.

This is `SimpleGraph.TowerData` with the attachment *vertex* of each stage replaced by an
attachment *set*. -/
def CliqueTowerData (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => CliqueTowerData V k × Finset (TowerV V k)

/-- **A tower of cone attachments.** `cliqueTower G k d` is the graph obtained from `G` by adding
`k` new vertices one after another, the `i`-th of them joined to the set of already-existing
vertices recorded in `d` (which may contain earlier new vertices).

When every attachment set is a clique of the graph existing at its stage — that is, when
`d` is `SimpleGraph.CliqueTowerData.IsSimplicial` — this is a graph presented by a simplicial
elimination ordering, read backwards. -/
def cliqueTower (G : SimpleGraph V) : (k : ℕ) → CliqueTowerData V k → SimpleGraph (TowerV V k)
  | 0, _ => G
  | k + 1, d => coneOn (cliqueTower G k d.1) d.2

/-- Adjacency in a clique tower is decidable, by recursion on the height of the tower. -/
instance instDecidableRelCliqueTower [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] :
    (k : ℕ) → (d : CliqueTowerData V k) → DecidableRel (cliqueTower G k d).Adj
  | 0, _ => inferInstanceAs (DecidableRel G.Adj)
  | k + 1, d =>
      letI := instDecidableEqTowerV (V := V) k
      letI := instDecidableRelCliqueTower (G := G) k d.1
      inferInstanceAs (DecidableRel (coneOn (cliqueTower G k d.1) d.2).Adj)

@[simp] lemma cliqueTower_zero (G : SimpleGraph V) (d : CliqueTowerData V 0) :
    cliqueTower G 0 d = G := rfl

@[simp] lemma cliqueTower_succ (G : SimpleGraph V) (k : ℕ) (d : CliqueTowerData V (k + 1)) :
    cliqueTower G (k + 1) d = coneOn (cliqueTower G k d.1) d.2 := rfl

/-- **The simplicial condition.** `d.IsSimplicial` says that at every stage of the tower the set of
old vertices to which the new vertex is attached is a clique *of the graph existing at that stage*.

This is the hypothesis of Kirov–Naimi's Lemma 1 imposed at each of the `k` steps; equivalently, it
says that reading the construction backwards deletes a simplicial vertex at every step. -/
def CliqueTowerData.IsSimplicial (G : SimpleGraph V) :
    (k : ℕ) → CliqueTowerData V k → Prop
  | 0, _ => True
  | k + 1, d =>
      (cliqueTower G k d.1).IsClique ((d.2 : Finset (TowerV V k)) : Set (TowerV V k)) ∧
        CliqueTowerData.IsSimplicial G k d.1

@[simp] lemma CliqueTowerData.isSimplicial_zero (G : SimpleGraph V) (d : CliqueTowerData V 0) :
    CliqueTowerData.IsSimplicial G 0 d := trivial

@[simp] lemma CliqueTowerData.isSimplicial_succ (G : SimpleGraph V) (k : ℕ)
    (d : CliqueTowerData V (k + 1)) :
    CliqueTowerData.IsSimplicial G (k + 1) d ↔
      (cliqueTower G k d.1).IsClique ((d.2 : Finset (TowerV V k)) : Set (TowerV V k)) ∧
        CliqueTowerData.IsSimplicial G k d.1 := Iff.rfl

end Tower

/-! ### The theorem -/

section Main

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Kostochka–Sidorenko, inductive form.** If `G` is enumeratively chromatic-choosable at `n` and
`d` is a simplicial tower of cone attachments over `G`, then the graph `cliqueTower G k d` built by
the tower is enumeratively chromatic-choosable at `n`.

The induction is on the height `k` of the tower; each step is Kirov–Naimi's Lemma 1
(`SimpleGraph.ECCAt.coneOn`) applied to the clique `d.2`. -/
theorem ecc_cliqueTower {n : ℕ} (hG : G.ECCAt n) :
    ∀ (k : ℕ) (d : CliqueTowerData V k), CliqueTowerData.IsSimplicial G k d →
      (cliqueTower G k d).ECCAt n
  | 0, _, _ => hG
  | k + 1, d, h =>
      letI := instDecidableEqTowerV (V := V) k
      letI := instFintypeTowerV (V := V) k
      letI := instDecidableRelCliqueTower (G := G) k d.1
      ECCAt.coneOn h.1 (ecc_cliqueTower hG k d.1 h.2)

/-- **The Kostochka–Sidorenko corollary** (Kirov–Naimi, Corollary to Lemma 1), in its simplicial
elimination ordering form: *a graph admitting a simplicial elimination ordering is enumeratively
chromatic-choosable at `n` for every `n`*.

Here the ordering is presented constructively and backwards: the graph is `cliqueTower G k d` for
an *empty* starting graph `G`, so all of its vertices are introduced by the tower, each one joined
to a clique of the graph built so far. The base case of the induction is
`SimpleGraph.ecc_of_isEmpty`, the step is Lemma 1.

Dirac's theorem — a graph is chordal (every cycle of length at least `4` has a chord) if and only
if it admits a simplicial elimination ordering — is what connects this to the usual statement
"every chordal graph is enumeratively chromatic-choosable at `n`". Dirac's theorem is a statement
about graph structure alone, involves no colorings, and is **not part of this development**. -/
theorem ecc_cliqueTower_of_isEmpty {V : Type u} [Fintype V] [DecidableEq V] [IsEmpty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ) (d : CliqueTowerData V k)
    (hd : CliqueTowerData.IsSimplicial G k d) : (cliqueTower G k d).ECCAt n :=
  ecc_cliqueTower (ecc_of_isEmpty G n) k d hd

/-- The Kostochka–Sidorenko corollary with the empty starting graph taken to be the concrete graph
`⊥ : SimpleGraph (Fin 0)`: every graph built from nothing by successively attaching a vertex to a
clique is enumeratively chromatic-choosable at `n`, for every `n`. -/
theorem ecc_cliqueTower_fin_zero (n k : ℕ) (d : CliqueTowerData (Fin 0) k)
    (hd : CliqueTowerData.IsSimplicial (⊥ : SimpleGraph (Fin 0)) k d) :
    (cliqueTower (⊥ : SimpleGraph (Fin 0)) k d).ECCAt n :=
  ecc_cliqueTower_of_isEmpty _ n k d hd

end Main

/-! ### Pendant towers are the singleton case -/

section Pendant

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The clique tower data attaching each new vertex to the *singleton* recorded by a pendant tower
datum. -/
def TowerData.toCliqueTowerData {V : Type u} : (k : ℕ) → TowerData V k → CliqueTowerData V k
  | 0, _ => PUnit.unit
  | k + 1, d => (TowerData.toCliqueTowerData k d.1, {d.2})

/-- **A pendant tower is a clique tower**: attaching a pendant vertex at `v` is coning off the
singleton `{v}`. -/
theorem pendantTower_eq_cliqueTower {V : Type u} (G : SimpleGraph V) :
    ∀ (k : ℕ) (d : TowerData V k),
      pendantTower G k d = cliqueTower G k (TowerData.toCliqueTowerData k d)
  | 0, _ => rfl
  | k + 1, d => by
      show (pendantTower G k d.1).addPendant d.2
        = coneOn (cliqueTower G k (TowerData.toCliqueTowerData k d.1)) {d.2}
      rw [pendantTower_eq_cliqueTower G k d.1, addPendant_eq_coneOn]

/-- Singletons are cliques, so the clique tower data coming from a pendant tower is always
simplicial — no hypothesis on `G` or on the attachment points is needed. -/
theorem isSimplicial_toCliqueTowerData {V : Type u} (G : SimpleGraph V) :
    ∀ (k : ℕ) (d : TowerData V k),
      CliqueTowerData.IsSimplicial G k (TowerData.toCliqueTowerData k d)
  | 0, _ => trivial
  | k + 1, d =>
      ⟨isClique_coe_singleton (G := cliqueTower G k (TowerData.toCliqueTowerData k d.1)) d.2,
       isSimplicial_toCliqueTowerData G k d.1⟩

/-- **Sanity check: Lemma 5's forward direction is a special case of Kostochka–Sidorenko.** A tower
of pendant attachments over a graph enumeratively chromatic-choosable at `n` is again
enumeratively chromatic-choosable at `n`, proved here through
`SimpleGraph.ecc_cliqueTower` rather than through
`SimpleGraph.ecc_pendantTower_iff`. -/
theorem ecc_pendantTower_of_cliqueTower {n : ℕ} (hG : G.ECCAt n) (k : ℕ)
    (d : TowerData V k) : (pendantTower G k d).ECCAt n := by
  letI := instDecidableEqTowerV (V := V) k
  letI := instFintypeTowerV (V := V) k
  letI := instDecidableRelPendantTower (G := G) k d
  letI := instDecidableRelCliqueTower (G := G) k (TowerData.toCliqueTowerData k d)
  refine (ecc_congr (G := pendantTower G k d)
    (G' := cliqueTower G k (TowerData.toCliqueTowerData k d)) (fun a b => ?_) n).mpr
    (ecc_cliqueTower hG k _ (isSimplicial_toCliqueTowerData G k d))
  rw [pendantTower_eq_cliqueTower G k d]

end Pendant

/-! ### Complete graphs, recovered from the corollary

Coning off *all* of the previous vertices at every stage builds the complete graphs from nothing,
so `SimpleGraph.ecc_top_fin` is itself a special case of the corollary. -/

section Complete

variable {V : Type u}

/-- The clique tower data joining each new vertex to *every* old vertex. The resulting tower over an
empty graph builds the complete graphs. -/
def univTowerData (V : Type u) [Fintype V] : (k : ℕ) → CliqueTowerData V k
  | 0 => PUnit.unit
  | k + 1 => (univTowerData V k, (univ : Finset (TowerV V k)))

/-- Attaching every new vertex to all the old ones, starting from an empty graph, produces the
complete graph at every stage. -/
theorem cliqueTower_univTowerData [Fintype V] [IsEmpty V] (k : ℕ) :
    cliqueTower (⊥ : SimpleGraph V) k (univTowerData V k) = (⊤ : SimpleGraph (TowerV V k)) := by
  induction k with
  | zero =>
      ext a b
      exact isEmptyElim (α := V) a
  | succ k ih =>
      show coneOn (cliqueTower (⊥ : SimpleGraph V) k (univTowerData V k)) univ = ⊤
      rw [ih]
      ext x y
      simpa using coneOn_top_univ_adj x y

/-- The "join to everything" tower is simplicial: at each stage the whole vertex set of a complete
graph is a clique. -/
theorem isSimplicial_univTowerData [Fintype V] [IsEmpty V] (k : ℕ) :
    CliqueTowerData.IsSimplicial (⊥ : SimpleGraph V) k (univTowerData V k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      refine ⟨?_, ih⟩
      show (cliqueTower (⊥ : SimpleGraph V) k (univTowerData V k)).IsClique
        ((univ : Finset (TowerV V k)) : Set (TowerV V k))
      rw [cliqueTower_univTowerData k]
      intro a _ b _ hab
      exact hab

/-- An equivalence of vertex types is an isomorphism of the complete graphs on them. -/
def topIsoTopOfEquiv {α β : Type*} (e : α ≃ β) :
    (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph β) where
  toEquiv := e
  map_rel_iff' := by
    intro a b
    simp

/-- The vertex type of a tower of height `k` over the empty type has exactly `k` elements. -/
def towerVEquivFin : (k : ℕ) → TowerV (Fin 0) k ≃ Fin k
  | 0 => Equiv.refl (Fin 0)
  | k + 1 => (Equiv.optionCongr (towerVEquivFin k)).trans (finSuccEquiv k).symm

/-- **Sanity check: complete graphs, from the Kostochka–Sidorenko corollary.** The complete graph
on `Fin m` is built from nothing by `m` cone attachments, each one over the (complete, hence
clique) set of all earlier vertices, so `SimpleGraph.ecc_top_fin` follows from
`SimpleGraph.ecc_cliqueTower_of_isEmpty`. -/
theorem ecc_top_fin_of_cliqueTower (m n : ℕ) : (⊤ : SimpleGraph (Fin m)).ECCAt n := by
  letI := instDecidableEqTowerV (V := Fin 0) m
  letI := instFintypeTowerV (V := Fin 0) m
  have h : (cliqueTower (⊥ : SimpleGraph (Fin 0)) m (univTowerData (Fin 0) m)).ECCAt n :=
    ecc_cliqueTower_of_isEmpty _ n m _ (isSimplicial_univTowerData m)
  have htop : (⊤ : SimpleGraph (TowerV (Fin 0) m)).ECCAt n :=
    (ecc_congr (G := cliqueTower (⊥ : SimpleGraph (Fin 0)) m (univTowerData (Fin 0) m))
      (G' := (⊤ : SimpleGraph (TowerV (Fin 0) m)))
      (fun a b => by rw [cliqueTower_univTowerData m]) n).mp h
  exact (ecc_iso (topIsoTopOfEquiv (towerVEquivFin m)) n).mp htop

end Complete

/-! ### Sanity checks -/

section Guards

/-- The two-step clique tower over the empty graph on `Fin 1`: first a pendant edge, then a vertex
joined to both of its endpoints. -/
private def triangleData : CliqueTowerData (Fin 1) 2 :=
  ((PUnit.unit, ({0} : Finset (Fin 1))), univ)

-- the triangle: `3 * 2 * 1 = 6` proper colorings from three colors
#guard (cliqueTower (⊥ : SimpleGraph (Fin 1)) 2 triangleData).colConst 3 = 6

-- and it really is the complete graph on its three vertices
example : ∀ a b : TowerV (Fin 1) 2,
    (cliqueTower (⊥ : SimpleGraph (Fin 1)) 2 triangleData).Adj a b ↔ a ≠ b := by decide

-- adding a fourth vertex joined to the whole triangle gives `K₄`: `4 * 3 * 2 * 1 = 24`
local instance : DecidableRel (cliqueTower (⊥ : SimpleGraph (Fin 1)) 3 (triangleData, univ)).Adj :=
  instDecidableRelCliqueTower 3 _

#guard (cliqueTower (⊥ : SimpleGraph (Fin 1)) 3 (triangleData, univ)).colConst 4 = 24

-- a pendant tower is the singleton case of a clique tower
example (v : Fin 1) : pendantTower (⊥ : SimpleGraph (Fin 1)) 1 (PUnit.unit, v)
    = cliqueTower (⊥ : SimpleGraph (Fin 1)) 1 (PUnit.unit, {v}) :=
  pendantTower_eq_cliqueTower _ 1 (PUnit.unit, v)

end Guards

end SimpleGraph
