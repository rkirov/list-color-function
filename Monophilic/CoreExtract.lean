/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.RubinStructure
import Monophilic.Theorem2

/-!
# Extracting the core, and recognizing a cycle or a theta

**Attribution.** Everything in this file serves the hard direction of **Rubin's theorem**
(A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West Coast
Conf. on Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congr. Numer. **26**,
Utilitas Math., Winnipeg, **1980**, 125–157, pp. 131–134). Nothing here is novel: both results are
classical facts that a paper states in a clause — "pass to the core", "a connected `2`-regular
graph is a cycle", "`C₁ ∪ P₁` is a theta graph" — and neither Rubin nor Kirov–Naimi prove them. What
is new is only the mechanization.

`Monophilic/RubinStructure.lean` records what the structural half of Rubin's argument still needs
beyond his steps 1–6, namely *"the passage from graph structure to `Monophilic.CoreIs`"*. This file
supplies two of the three pieces named there.

## The three results

* **The core exists.** `Monophilic.hasCore`: a connected finite graph `G` admits a graph `H`, on its
  own vertex type, which is connected, is either a single vertex or of minimum degree `≥ 2`, and
  satisfies `Monophilic.CoreIs G H`. The proof is the obvious induction on `Fintype.card V`: if some
  vertex has degree `≤ 1` — and, `G` being connected on more than one vertex, then exactly `1` —
  delete it, recurse, and put the deleted vertex back as the top of the pendant tower. Deleting a
  vertex of degree one keeps a connected graph connected, which is Mathlib's
  `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`.

* **A connected `2`-regular graph is a cycle.** `Monophilic.exists_iso_closePath_of_two_regular`:
  such a graph is isomorphic to `Monophilic.closePath k` for some `k ≥ 2`, i.e. to the cycle on
  `k + 1` vertices. The proof takes any cycle walk (which exists by
  `Monophilic.exists_isCycle_of_two_le_degree`), observes that its vertices already carry two
  neighbours each so that the graph has no other vertices, and reads off the isomorphism.

* **A cycle plus a chord path is a theta graph.**
  `Monophilic.nonempty_iso_thetaGen_of_paths`: a graph that is exactly the union of three internally
  disjoint paths of lengths `a`, `b`, `c` joining two distinct vertices is `Monophilic.thetaGen a b
  c`. Rubin's `C₁ ∪ P₁` is of that form, with the two arcs of `C₁` and `P₁` as the three paths. In
  the shape `(2, 2, 2m)` the target can be moved onto this development's own model of the family,
  `Monophilic.theta m`, by `Monophilic.nonempty_iso_theta_of_iso_thetaGen`.

## The index form of `pathG` and `closePath`

Both halves, and the theta case still to come, want the vertices of a path or cycle addressed by a
number rather than by a nest of `Option`s. `Monophilic.pathNum k` numbers `PathV k` from
`pathEnd k = 0` up to `pathStart k = k`, `Monophilic.pathAt k` inverts it, and

* `Monophilic.pathG_adj_num` : `pathG k` joins consecutive numbers;
* `Monophilic.closePath_adj_num` : `closePath k` joins consecutive numbers and also `0` to `k`.

The second is the convention that has repeatedly bitten this development — `closePath k` is the
cycle on `k + 1` vertices, not on `k` — so it is checked by `decide` at several `k` below before
anything is proved from it.

## Main definitions

* `Monophilic.pathNum`, `Monophilic.pathAt` : the numbering of `PathV k` and its inverse
* `Monophilic.HasCore` : `G` has a core — the conclusion of `Monophilic.hasCore`
* `Monophilic.armIdx`, `Monophilic.tgArm`, `Monophilic.tgArmLen`, `Monophilic.ThetaStep` : the arms
  of `thetaGen a b c`, on indices
* `Monophilic.IsThetaArms` : `H` is exactly the union of three internally disjoint paths
* `Monophilic.armVertex` : the vertex of `H` at a given index of the `thetaGen` layout

## Main results

* `Monophilic.addPendantIso` : isomorphisms lift through `SimpleGraph.addPendant`
* `Monophilic.isoAddPendantOfDegreeOne` : a graph with a vertex of degree one is a pendant
  attachment to the graph with that vertex removed
* `Monophilic.pathG_adj_num`, `Monophilic.closePath_adj_num` : path and cycle adjacency, on indices
* `Monophilic.hasCore` : **every connected finite graph has a core**
* `Monophilic.nonempty_iso_closePath_of_index` : a cyclic indexing of the vertices of a graph, in
  which adjacency is exactly cyclic adjacency of indices, is an isomorphism onto `closePath k`
* `Monophilic.exists_iso_closePath_of_two_regular` : **a connected `2`-regular graph is a cycle**
* `Monophilic.armStepB_iff_armIdx`, `Monophilic.thetaGen_adj_iff` : the edges of `thetaGen a b c`
  are exactly the steps along its three arms, and nothing else
* `Monophilic.nonempty_iso_thetaGen_of_index`, `Monophilic.nonempty_iso_thetaGen_of_arms`,
  `Monophilic.nonempty_iso_thetaGen_of_paths` : **a graph presented as three internally disjoint
  paths between two branch vertices is a theta graph**, in three increasingly explicit forms
* `Monophilic.nonempty_iso_thetaOf_thetaGen`, `Monophilic.nonempty_iso_theta_thetaGen`,
  `Monophilic.nonempty_iso_theta_of_iso_thetaGen` : the shape `(2, 2, 2m)`, moved onto
  `Monophilic.theta m`
-/

open Finset SimpleGraph

namespace Monophilic

/-! ### Pendant attachments and isomorphisms -/

/-- Isomorphisms lift through `SimpleGraph.addPendant`: attaching a pendant vertex at `v` on one
side and at `e v` on the other gives isomorphic graphs. -/
def addPendantIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (v : V) :
    G.addPendant v ≃g H.addPendant (e v) where
  toEquiv := Equiv.optionCongr e.toEquiv
  map_rel_iff' := by
    rintro (_ | a) (_ | b) <;>
      simp [SimpleGraph.addPendant, SimpleGraph.addPendantAdj, Equiv.optionCongr, e.map_rel_iff]

/-- Removing a vertex from `V` and then adjoining a fresh point returns `V`. -/
def complSingletonEquiv {V : Type} [DecidableEq V] (v : V) : Option ↥({v}ᶜ : Set V) ≃ V where
  toFun := fun o => o.elim v Subtype.val
  invFun := fun w => if h : w = v then none else some ⟨w, h⟩
  left_inv := by
    rintro (_ | ⟨w, hw⟩)
    · simp
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
      simp [hw]
  right_inv := by intro w; by_cases h : w = v <;> simp [h]

/-- **A graph with a vertex of degree one is a pendant attachment.** If `u` is the unique neighbour
of `v`, then `G` is `G` with `v` deleted, plus a new vertex attached at `u`. This is the step of the
core induction, read backwards. -/
def isoAddPendantOfDegreeOne {V : Type} [DecidableEq V] {G : SimpleGraph V} {v u : V}
    (hu : u ≠ v) (huniq : ∀ w, G.Adj v w ↔ w = u) :
    (G.induce ({v}ᶜ : Set V)).addPendant ⟨u, hu⟩ ≃g G where
  toEquiv := complSingletonEquiv v
  map_rel_iff' := by
    rintro (_ | ⟨a, ha⟩) (_ | ⟨b, hb⟩) <;>
      simp_all [complSingletonEquiv, SimpleGraph.addPendant, SimpleGraph.addPendantAdj, G.adj_comm]

/-! ### Every connected finite graph has a core -/

/-- **`G` has a core**: a graph `H` on its own vertex type which is connected, is either a single
vertex or has minimum degree at least `2`, and of which `G` is a pendant tower
(`Monophilic.CoreIs`).

The three instance arguments have to be carried by the existential because `Monophilic.CoreIs`
takes them; only the vertex type `W` and the graph `H` are mathematical content. -/
def HasCore {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W) (_ : DecidableRel H.Adj),
    H.Connected ∧ (Fintype.card W = 1 ∨ ∀ w : W, 2 ≤ H.degree w) ∧ CoreIs G H

private theorem hasCore_aux : ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], Fintype.card V ≤ n → G.Connected → HasCore G := by
  intro n
  induction n with
  | zero =>
      intro V _ _ G _ hcard hconn
      have := Fintype.card_pos_iff.mpr hconn.nonempty
      omega
  | succ n ih =>
      intro V _ _ G _ hcard hconn
      by_cases hdeg : ∀ w : V, 2 ≤ G.degree w
      · exact ⟨V, ‹_›, ‹_›, G, ‹_›, hconn, Or.inr hdeg, 0, PUnit.unit, ⟨Iso.refl⟩⟩
      by_cases hcard1 : Fintype.card V = 1
      · exact ⟨V, ‹_›, ‹_›, G, ‹_›, hconn, Or.inl hcard1, 0, PUnit.unit, ⟨Iso.refl⟩⟩
      -- otherwise `2 ≤ card V`, and some vertex has degree exactly one
      push Not at hdeg
      obtain ⟨v, hv⟩ := hdeg
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
      have h2 : 2 ≤ Fintype.card V := by omega
      haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp h2
      have hdegpos : 0 < G.degree v :=
        lt_of_lt_of_le hconn.preconnected.minDegree_pos_of_nontrivial (G.minDegree_le_degree v)
      have hdeg1 : G.degree v = 1 := by omega
      obtain ⟨u, hadj, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg1
      have hune : u ≠ v := (G.ne_of_adj hadj).symm
      have huiff : ∀ w, G.Adj v w ↔ w = u := fun w => ⟨fun h => huniq w h, fun h => h ▸ hadj⟩
      have hconn' : (G.induce ({v}ᶜ : Set V)).Connected :=
        hconn.induce_compl_singleton_of_degree_eq_one hdeg1
      have hcard' : Fintype.card ↥({v}ᶜ : Set V) + 1 = Fintype.card V := by
        have e1 : Fintype.card ↥({v}ᶜ : Set V) = Fintype.card V - Fintype.card ↥({v} : Set V) :=
          Fintype.card_compl_set _
        have e2 : Fintype.card ↥({v} : Set V) = 1 := by simp
        omega
      obtain ⟨W, _, _, H, _, hHconn, hHdeg, k, d, ⟨e⟩⟩ :=
        ih (G.induce ({v}ᶜ : Set V)) (by omega) hconn'
      exact ⟨W, ‹_›, ‹_›, H, ‹_›, hHconn, hHdeg, k + 1, ⟨d, e ⟨u, hune⟩⟩,
        ⟨(isoAddPendantOfDegreeOne hune huiff).symm.trans (addPendantIso e ⟨u, hune⟩)⟩⟩

/-- **Every connected finite graph has a core.** Delete vertices of degree one until none is left;
what remains is connected, and is either a single vertex or of minimum degree at least `2`. Read
backwards, the deletions are a `SimpleGraph.pendantTower`, so the graph one started from is
`Monophilic.CoreIs` over the graph one ends with.

Classical, and assumed without proof wherever "the core" is used: Kirov–Naimi's Lemma 5 speaks of
"the core" of a graph, and Rubin's argument (Erdős–Rubin–Taylor 1980, pp. 131–134) begins by
passing to it. Not novel. -/
theorem hasCore {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) : HasCore G :=
  hasCore_aux (Fintype.card V) G le_rfl hG

/-! ### Numbering the vertices of a path

`PathV k` is `Unit` wrapped in `k` copies of `Option`; `Monophilic.pathNum` turns such a vertex into
its distance from `pathEnd k`. Because `PathV (k+1)` and `Option (PathV k)` are definitionally but
not syntactically equal, everything below is written by the equation compiler or crossed with
`show`; `rw` and `simp` do not see through the unfolding. -/

/-- The index of a vertex of `pathG k`, counted from `pathEnd k` (which gets `0`) to `pathStart k`
(which gets `k`). -/
def pathNum : (k : ℕ) → PathV k → ℕ
  | 0, _ => 0
  | _ + 1, none => 0
  | k + 1, some w => pathNum k w + 1

/-- The vertex of `pathG k` at index `i`; the inverse of `Monophilic.pathNum` on `i ≤ k`. -/
def pathAt : (k : ℕ) → ℕ → PathV k
  | 0, _ => ()
  | _ + 1, 0 => none
  | k + 1, i + 1 => some (pathAt k i)

@[simp] lemma pathNum_none (k : ℕ) : pathNum (k + 1) none = 0 := rfl

@[simp] lemma pathNum_some (k : ℕ) (w : PathV k) :
    pathNum (k + 1) (some w) = pathNum k w + 1 := rfl

theorem pathNum_le : ∀ (k : ℕ) (v : PathV k), pathNum k v ≤ k
  | 0, _ => le_rfl
  | _ + 1, none => Nat.zero_le _
  | k + 1, some w => Nat.succ_le_succ (pathNum_le k w)

theorem pathAt_pathNum : ∀ (k : ℕ) (v : PathV k), pathAt k (pathNum k v) = v
  | 0, () => rfl
  | _ + 1, none => rfl
  | k + 1, some w => by
      show (some (pathAt k (pathNum k w)) : Option (PathV k)) = some w
      rw [pathAt_pathNum k w]

theorem pathNum_pathAt : ∀ (k i : ℕ), i ≤ k → pathNum k (pathAt k i) = i
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (by omega)
  | _ + 1, 0, _ => rfl
  | k + 1, i + 1, h => by
      show pathNum k (pathAt k i) + 1 = i + 1
      rw [pathNum_pathAt k i (by omega)]

theorem pathNum_injective (k : ℕ) : Function.Injective (pathNum k) := by
  intro a b h
  rw [← pathAt_pathNum k a, ← pathAt_pathNum k b, h]

theorem pathNum_pathEnd : ∀ (k : ℕ), pathNum k (pathEnd k) = 0
  | 0 => rfl
  | _ + 1 => rfl

theorem pathNum_pathStart : ∀ (k : ℕ), pathNum k (pathStart k) = k
  | 0 => rfl
  | k + 1 => by
      show pathNum k (pathStart k) + 1 = k + 1
      rw [pathNum_pathStart k]

theorem eq_pathEnd_iff {k : ℕ} (a : PathV k) : a = pathEnd k ↔ pathNum k a = 0 :=
  ⟨fun h => by rw [h, pathNum_pathEnd],
   fun h => pathNum_injective k (by rw [h, pathNum_pathEnd])⟩

theorem eq_pathStart_iff {k : ℕ} (a : PathV k) : a = pathStart k ↔ pathNum k a = k :=
  ⟨fun h => by rw [h, pathNum_pathStart],
   fun h => pathNum_injective k (by rw [h, pathNum_pathStart])⟩

/-- **The path, on indices.** Two vertices of `pathG k` are adjacent exactly when their indices
differ by one. -/
theorem pathG_adj_num : ∀ (k : ℕ) (a b : PathV k),
    (pathG k).Adj a b ↔ (pathNum k a + 1 = pathNum k b ∨ pathNum k b + 1 = pathNum k a)
  | 0, a, b => by
      have h : a = b := Subsingleton.elim a b
      simp [pathG_zero, h]
  | k + 1, none, none => by
      show ((pathG k).addPendant (pathEnd k)).Adj none none ↔ _
      simp [SimpleGraph.addPendant]
  | k + 1, none, some b => by
      show (b = pathEnd k) ↔ (0 + 1 = pathNum k b + 1 ∨ pathNum k b + 1 + 1 = 0)
      rw [eq_pathEnd_iff]
      omega
  | k + 1, some a, none => by
      show (a = pathEnd k) ↔ (pathNum k a + 1 + 1 = 0 ∨ 0 + 1 = pathNum k a + 1)
      rw [eq_pathEnd_iff]
      omega
  | k + 1, some a, some b => by
      show (pathG k).Adj a b ↔
        (pathNum k a + 1 + 1 = pathNum k b + 1 ∨ pathNum k b + 1 + 1 = pathNum k a + 1)
      rw [pathG_adj_num k a b]
      omega

/-- **The cycle, on indices.** For `k ≥ 2` the vertices of `closePath k` — the cycle on `k + 1`
vertices — are adjacent exactly when their indices differ by one, or are `0` and `k`. -/
theorem closePath_adj_num (k : ℕ) (hk : 2 ≤ k) (a b : PathV k) :
    (closePath k).Adj a b ↔
      (pathNum k a + 1 = pathNum k b ∨ pathNum k b + 1 = pathNum k a ∨
        (pathNum k a = 0 ∧ pathNum k b = k) ∨ (pathNum k b = 0 ∧ pathNum k a = k)) := by
  rw [closePath_adj, pathG_adj_num]
  have ha := pathNum_le k a
  have hb := pathNum_le k b
  constructor
  · rintro (h | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
    · omega
    · rw [eq_pathStart_iff] at h1; rw [eq_pathEnd_iff] at h2; omega
    · rw [eq_pathEnd_iff] at h1; rw [eq_pathStart_iff] at h2; omega
  · rintro (h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨fun hab => by rw [hab] at h1; omega,
        Or.inr ⟨(eq_pathEnd_iff a).mpr h1, (eq_pathStart_iff b).mpr h2⟩⟩
    · exact Or.inr ⟨fun hab => by rw [hab] at h2; omega,
        Or.inl ⟨(eq_pathStart_iff a).mpr h2, (eq_pathEnd_iff b).mpr h1⟩⟩

/-! ### A connected `2`-regular graph is a cycle -/

/-- Two known distinct neighbours of a vertex of degree `2` are all of its neighbours. -/
theorem adj_eq_of_degree_two {W : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {v x y : W} (hdeg : H.degree v = 2) (hx : H.Adj v x) (hy : H.Adj v y)
    (hxy : x ≠ y) : ∀ w, H.Adj v w → w = x ∨ w = y := by
  have hsub : ({x, y} : Finset W) ⊆ H.neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [hx, hy]
  have heq : ({x, y} : Finset W) = H.neighborFinset v :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hxy]; exact hdeg.le)
  intro w hw
  have hmem : w ∈ ({x, y} : Finset W) := by rw [heq]; simpa using hw
  simpa using hmem

/-- A set closed under passing to neighbours, containing one endpoint of a walk, contains the
other. -/
theorem mem_of_walk {W : Type} {H : SimpleGraph W} {S : Set W}
    (hclosed : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S) :
    ∀ {a b : W} (_ : H.Walk a b), a ∈ S → b ∈ S := by
  intro a b p
  induction p with
  | nil => exact id
  | cons h _ ih => exact fun ha => ih (hclosed _ ha _ h)

/-- **A cyclic indexing makes a graph a cycle.** If the vertices of `H` are listed injectively and
surjectively as `f 0, …, f k` with `k ≥ 2`, and two of them are adjacent exactly when their indices
are consecutive or are `0` and `k`, then `H` is the cycle on `k + 1` vertices. -/
theorem nonempty_iso_closePath_of_index {W : Type} {H : SimpleGraph W} {k : ℕ} (hk : 2 ≤ k)
    (f : ℕ → W) (hinj : Set.InjOn f (Set.Iic k)) (hsurj : ∀ w, ∃ i, i ≤ k ∧ f i = w)
    (hadj : ∀ i, i ≤ k → ∀ j, j ≤ k → (H.Adj (f i) (f j) ↔
      (i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j = k) ∨ (j = 0 ∧ i = k)))) :
    Nonempty (H ≃g closePath k) := by
  have hbij : Function.Bijective (fun p : PathV k => f (pathNum k p)) := by
    constructor
    · intro a b hab
      exact pathNum_injective k (hinj (pathNum_le k a) (pathNum_le k b) hab)
    · intro w
      obtain ⟨i, hi, rfl⟩ := hsurj w
      exact ⟨pathAt k i, by simp only []; rw [pathNum_pathAt k i hi]⟩
  refine ⟨SimpleGraph.Iso.symm ⟨Equiv.ofBijective _ hbij, ?_⟩⟩
  intro a b
  show H.Adj (f (pathNum k a)) (f (pathNum k b)) ↔ (closePath k).Adj a b
  rw [closePath_adj_num k hk, hadj _ (pathNum_le k a) _ (pathNum_le k b)]

/-- **A connected `2`-regular graph is a cycle.** It is isomorphic to `Monophilic.closePath k` —
the cycle on `k + 1` vertices — for some `k ≥ 2`.

Take any cycle walk, which exists because the minimum degree is at least `2`
(`Monophilic.exists_isCycle_of_two_le_degree`). Each of its vertices already has two neighbours on
it, and has degree `2`, so it has no others; the vertices of the cycle walk are therefore closed
under adjacency, and by connectedness they are all of `W`. Reading the walk off as an indexing
gives the isomorphism.

Classical, and used without proof wherever a paper says "the core is a cycle": in particular this
is the step of **Rubin's theorem** (Erdős–Rubin–Taylor 1980, pp. 131–134) at which a core with no
extra edge is declared to be an even cycle. Not novel. -/
theorem exists_iso_closePath_of_two_regular {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hconn : H.Connected)
    (hdeg : ∀ w : W, H.degree w = 2) : ∃ k, 2 ≤ k ∧ Nonempty (H ≃g closePath k) := by
  obtain ⟨v, c, hc⟩ := exists_isCycle_of_two_le_degree hconn (fun w => (hdeg w).ge)
  refine ⟨c.length - 1, two_le_cycleWalk_bound hc, ?_⟩
  set k := c.length - 1 with hkdef
  have hk : 2 ≤ k := two_le_cycleWalk_bound hc
  set f : ℕ → W := c.getVert with hfdef
  have hinj : Set.InjOn f (Set.Iic k) := cycleWalk_injOn hc
  have hstep : ∀ i, i < k → H.Adj (f i) (f (i + 1)) := fun i hi => cycleWalk_adj c hi
  have hclose : H.Adj (f k) (f 0) := cycleWalk_closes hc
  -- the two cyclic neighbours of the vertex at index `i`
  have hnext : ∀ i, i ≤ k → H.Adj (f i) (f (if i = k then 0 else i + 1)) := by
    intro i hi
    by_cases h : i = k
    · rw [if_pos h, h]; exact hclose
    · rw [if_neg h]; exact hstep i (by omega)
  have hprev : ∀ i, i ≤ k → H.Adj (f i) (f (if i = 0 then k else i - 1)) := by
    intro i hi
    by_cases h : i = 0
    · rw [if_pos h, h]; exact hclose.symm
    · rw [if_neg h]
      have h2 := hstep (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at h2
      exact h2.symm
  have hnbr : ∀ i, i ≤ k → ∀ w, H.Adj (f i) w →
      w = f (if i = 0 then k else i - 1) ∨ w = f (if i = k then 0 else i + 1) := by
    intro i hi
    refine adj_eq_of_degree_two (hdeg (f i)) (hprev i hi) (hnext i hi) ?_
    intro hEq
    have h1 : (if i = 0 then k else i - 1) ∈ Set.Iic k := by
      simp only [Set.mem_Iic]; split_ifs <;> omega
    have h2 : (if i = k then 0 else i + 1) ∈ Set.Iic k := by
      simp only [Set.mem_Iic]; split_ifs <;> omega
    have h3 := hinj h1 h2 hEq
    split_ifs at h3 <;> omega
  -- so the vertices of the cycle walk are closed under adjacency, hence are everything
  have hsurj : ∀ w, ∃ i, i ≤ k ∧ f i = w := by
    have hclosed : ∀ a ∈ f '' (Set.Iic k), ∀ b, H.Adj a b → b ∈ f '' (Set.Iic k) := by
      rintro a ⟨i, hi, rfl⟩ b hb
      simp only [Set.mem_Iic] at hi
      rcases hnbr i hi b hb with rfl | rfl
      · exact ⟨_, by simp only [Set.mem_Iic]; split_ifs <;> omega, rfl⟩
      · exact ⟨_, by simp only [Set.mem_Iic]; split_ifs <;> omega, rfl⟩
    intro w
    obtain ⟨p⟩ := hconn.preconnected (f 0) w
    obtain ⟨i, hi, hiw⟩ := mem_of_walk hclosed p ⟨0, by simp, rfl⟩
    exact ⟨i, by simpa using hi, hiw⟩
  refine nonempty_iso_closePath_of_index hk f hinj hsurj ?_
  intro i hi j hj
  constructor
  · intro h
    rcases hnbr i hi (f j) h with h' | h'
    · have h1 : (if i = 0 then k else i - 1) ∈ Set.Iic k := by
        simp only [Set.mem_Iic]; split_ifs <;> omega
      have := hinj (Set.mem_Iic.mpr hj) h1 h'
      split_ifs at this <;> omega
    · have h2 : (if i = k then 0 else i + 1) ∈ Set.Iic k := by
        simp only [Set.mem_Iic]; split_ifs <;> omega
      have := hinj (Set.mem_Iic.mpr hj) h2 h'
      split_ifs at this <;> omega
  · rintro (h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · subst h; exact hstep i (by omega)
    · subst h; exact (hstep j (by omega)).symm
    · subst h1; subst h2; exact hclose.symm
    · subst h1; subst h2; exact hclose

/-! ### Theta graphs: reading `thetaGen a b c` off its three arms

`Monophilic.thetaGen a b c` is laid out on `Fin (a+b+c-1)` by an index formula
(`Monophilic.thetaGenAdjB`), which says nothing directly about arms. The block below turns that
formula into the statement a proof wants — *the graph is the union of three internally disjoint
paths between two branch vertices, and has no other edge* — and then runs the identification in
reverse: any graph presented that way **is** `thetaGen a b c`.

`Monophilic.armIdx o len ps pt i` is the index of the vertex at position `i` along an arm of length
`len` whose interior vertices are `o, o+1, …, o+len-2` and whose ends are the branch vertices `ps`
and `pt`. The three arms of `thetaGen a b c` are this with

* `o = 0`, `len = a`; `o = a-1`, `len = b`; `o = a+b-2`, `len = c`,

and `ps = a+b+c-3`, `pt = a+b+c-2`. That reading of the layout — `Monophilic.thetaGen_adj_iff` — is
**checked by `decide` at every shape with `1 ≤ a, b, c ≤ 4`**, and at `(2,2,6)` and `(3,4,5)`, in
the guard block at the end of this file, because it is exactly the kind of index convention this
development has had refuted before. -/


/-- Index of position `i` along an arm of length `len` whose interior vertices are indexed
`o, o+1, …, o+len-2`, and which runs from the branch vertex `ps` to the branch vertex `pt`. -/
def armIdx (o len ps pt i : ℕ) : ℕ :=
  if i = 0 then ps else if i = len then pt else o + (i - 1)

variable {o len ps pt : ℕ}

@[simp] lemma armIdx_zero : armIdx o len ps pt 0 = ps := rfl

lemma armIdx_len (h : 1 ≤ len) : armIdx o len ps pt len = pt := by
  unfold armIdx; rw [if_neg (by omega), if_pos rfl]

lemma armIdx_mid {i : ℕ} (h1 : 1 ≤ i) (h2 : i < len) : armIdx o len ps pt i = o + (i - 1) := by
  unfold armIdx; rw [if_neg (by omega), if_neg (by omega)]

/-- The positions of an arm get distinct indices. -/
lemma armIdx_inj (hlen : 1 ≤ len) (hgap : o + len ≤ ps + 1) (hpp : ps < pt)
    {i j : ℕ} (hi : i ≤ len) (hj : j ≤ len) (h : armIdx o len ps pt i = armIdx o len ps pt j) :
    i = j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    · rcases eq_or_lt_of_le hj with rfl | hjl
      · rw [armIdx_zero, armIdx_len hlen] at h; omega
      · rw [armIdx_zero, armIdx_mid hj0 hjl] at h; omega
  rcases eq_or_lt_of_le hi with rfl | hil
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [armIdx_zero, armIdx_len hlen] at h; omega
    · rcases eq_or_lt_of_le hj with rfl | hjl
      · rfl
      · rw [armIdx_len hlen, armIdx_mid hj0 hjl] at h; omega
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [armIdx_zero, armIdx_mid hi0 hil] at h; omega
    · rcases eq_or_lt_of_le hj with rfl | hjl
      · rw [armIdx_len hlen, armIdx_mid hi0 hil] at h; omega
      · rw [armIdx_mid hi0 hil, armIdx_mid hj0 hjl] at h; omega

/-- **The arm, unfolded.** `armStepB` describes exactly the consecutive pairs of `armIdx`. -/
lemma armStepB_iff_armIdx (hlen : 1 ≤ len) (hgap : o + len ≤ ps + 1) (hpp : ps < pt) (x y : ℕ) :
    armStepB o (len - 1) ps pt x y = true ↔
      ∃ i < len, x = armIdx o len ps pt i ∧ y = armIdx o len ps pt (i + 1) := by
  unfold armStepB
  split_ifs with hm
  · have hlen1 : len = 1 := by omega
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨0, by omega, armIdx_zero.symm, by rw [show (0 : ℕ) + 1 = len by omega, armIdx_len hlen]⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      have hi0 : i = 0 := by omega
      subst hi0
      exact ⟨armIdx_zero, by rw [show (0 : ℕ) + 1 = len by omega, armIdx_len hlen]⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff]
    constructor
    · rintro ((⟨rfl, rfl⟩ | ⟨⟨hox, rfl⟩, hlt⟩) | ⟨rfl, rfl⟩)
      · exact ⟨0, by omega, armIdx_zero.symm,
          by rw [armIdx_mid (by omega) (by omega)]; omega⟩
      · refine ⟨x - o + 1, by omega, ?_, ?_⟩
        · rw [armIdx_mid (by omega) (by omega)]; omega
        · rw [armIdx_mid (by omega) (by omega)]; omega
      · refine ⟨len - 1, by omega, ?_, ?_⟩
        · rw [armIdx_mid (by omega) (by omega)]; omega
        · rw [show len - 1 + 1 = len by omega, armIdx_len hlen]
    · rintro ⟨i, hi, rfl, rfl⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact Or.inl (Or.inl ⟨armIdx_zero, by rw [armIdx_mid (by omega) (by omega)]; omega⟩)
      by_cases hlast : i + 1 = len
      · refine Or.inr ⟨?_, ?_⟩
        · rw [armIdx_mid hi0 (by omega)]; omega
        · rw [hlast, armIdx_len hlen]
      · refine Or.inl (Or.inr ⟨⟨?_, ?_⟩, ?_⟩)
        · rw [armIdx_mid hi0 (by omega)]; omega
        · rw [armIdx_mid hi0 (by omega), armIdx_mid (by omega) (by omega)]; omega
        · rw [armIdx_mid (by omega) (by omega)]; omega

/-- The index along the `t`-th arm of `thetaGen a b c` of the vertex at position `i`. -/
def tgArm (a b c : ℕ) : ℕ → ℕ → ℕ
  | 0 => armIdx 0 a (a + b + c - 3) (a + b + c - 2)
  | 1 => armIdx (a - 1) b (a + b + c - 3) (a + b + c - 2)
  | _ => armIdx (a + b - 2) c (a + b + c - 3) (a + b + c - 2)

/-- The length of the `t`-th arm of `thetaGen a b c`. -/
def tgArmLen (a b c : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | _ => c

/-- `x` and `y` are consecutive positions along one of the three arms. -/
def ThetaStep (a b c x y : ℕ) : Prop :=
  ∃ t < 3, ∃ i < tgArmLen a b c t, x = tgArm a b c t i ∧ y = tgArm a b c t (i + 1)

section
variable {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
include ha hb hc

lemma tgArm_inj {t : ℕ} (ht : t < 3) {i j : ℕ} (hi : i ≤ tgArmLen a b c t)
    (hj : j ≤ tgArmLen a b c t) (h : tgArm a b c t i = tgArm a b c t j) : i = j := by
  match t, ht with
  | 0, _ => exact armIdx_inj ha (by omega) (by omega) hi hj h
  | 1, _ => exact armIdx_inj hb (by omega) (by omega) hi hj h
  | 2, _ => exact armIdx_inj hc (by omega) (by omega) hi hj h

lemma thetaStep_ne {x y : ℕ} (h : ThetaStep a b c x y) : x ≠ y := by
  obtain ⟨t, ht, i, hi, rfl, rfl⟩ := h
  intro heq
  have := tgArm_inj ha hb hc ht (le_of_lt hi) (by omega) heq
  omega

lemma thetaGenAdjB_iff (x y : ℕ) : thetaGenAdjB a b c x y = true ↔ ThetaStep a b c x y := by
  unfold thetaGenAdjB
  rw [Bool.or_eq_true, Bool.or_eq_true,
    armStepB_iff_armIdx ha (by omega) (by omega), armStepB_iff_armIdx hb (by omega) (by omega),
    armStepB_iff_armIdx hc (by omega) (by omega)]
  constructor
  · rintro ((⟨i, hi, h1, h2⟩ | ⟨i, hi, h1, h2⟩) | ⟨i, hi, h1, h2⟩)
    · exact ⟨0, by omega, i, hi, h1, h2⟩
    · exact ⟨1, by omega, i, hi, h1, h2⟩
    · exact ⟨2, by omega, i, hi, h1, h2⟩
  · rintro ⟨t, ht, i, hi, h1, h2⟩
    match t, ht with
    | 0, _ => exact Or.inl (Or.inl ⟨i, hi, h1, h2⟩)
    | 1, _ => exact Or.inl (Or.inr ⟨i, hi, h1, h2⟩)
    | 2, _ => exact Or.inr ⟨i, hi, h1, h2⟩

/-- **`thetaGen a b c` is the union of its three arms and nothing else.** -/
theorem thetaGen_adj_iff (u v : TGV a b c) :
    (thetaGen a b c).Adj u v ↔ (ThetaStep a b c u.val v.val ∨ ThetaStep a b c v.val u.val) := by
  constructor
  · rintro ⟨-, h⟩
    rcases h with h | h
    · exact Or.inl ((thetaGenAdjB_iff ha hb hc _ _).mp h)
    · exact Or.inr ((thetaGenAdjB_iff ha hb hc _ _).mp h)
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h with h | h
      · exact fun huv => thetaStep_ne ha hb hc h (by rw [huv])
      · exact fun huv => (thetaStep_ne ha hb hc h) (by rw [huv])
    · rcases h with h | h
      · exact Or.inl ((thetaGenAdjB_iff ha hb hc _ _).mpr h)
      · exact Or.inr ((thetaGenAdjB_iff ha hb hc _ _).mpr h)

end

lemma armIdx_le {o len ps pt i : ℕ} (hlen : 1 ≤ len) (hgap : o + len ≤ ps + 1) (hpp : ps < pt)
    (hi : i ≤ len) : armIdx o len ps pt i ≤ pt := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [armIdx_zero]; omega
  rcases eq_or_lt_of_le hi with rfl | hil
  · rw [armIdx_len hlen]
  · rw [armIdx_mid hi0 hil]; omega

section
variable {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
include ha hb hc

lemma tgArm_lt {t : ℕ} (ht : t < 3) {i : ℕ} (hi : i ≤ tgArmLen a b c t) :
    tgArm a b c t i < a + b + c - 1 := by
  have key : ∀ o len : ℕ, 1 ≤ len → o + len ≤ (a + b + c - 3) + 1 → i ≤ len →
      armIdx o len (a + b + c - 3) (a + b + c - 2) i < a + b + c - 1 := by
    intro o len h1 h2 h3
    have := armIdx_le h1 h2 (show a + b + c - 3 < a + b + c - 2 by omega) h3
    omega
  match t, ht with
  | 0, _ => exact key 0 a ha (by omega) hi
  | 1, _ => exact key (a - 1) b hb (by omega) hi
  | 2, _ => exact key (a + b - 2) c hc (by omega) hi

lemma tgArm_surj {x : ℕ} (hx : x < a + b + c - 1) :
    ∃ t, t < 3 ∧ ∃ i, i ≤ tgArmLen a b c t ∧ tgArm a b c t i = x := by
  by_cases h1 : x = a + b + c - 2
  · exact ⟨0, by omega, a, by simp [tgArmLen], by
      show armIdx 0 a (a + b + c - 3) (a + b + c - 2) a = x
      rw [armIdx_len ha]; omega⟩
  by_cases h2 : x = a + b + c - 3
  · exact ⟨0, by omega, 0, by simp [tgArmLen], by
      show armIdx 0 a (a + b + c - 3) (a + b + c - 2) 0 = x
      rw [armIdx_zero]; omega⟩
  by_cases h3 : x < a - 1
  · exact ⟨0, by omega, x + 1, by simp only [tgArmLen]; omega, by
      show armIdx 0 a (a + b + c - 3) (a + b + c - 2) (x + 1) = x
      rw [armIdx_mid (by omega) (by omega)]; omega⟩
  by_cases h4 : x < a + b - 2
  · exact ⟨1, by omega, x - (a - 1) + 1, by simp only [tgArmLen]; omega, by
      show armIdx (a - 1) b (a + b + c - 3) (a + b + c - 2) (x - (a - 1) + 1) = x
      rw [armIdx_mid (by omega) (by omega)]; omega⟩
  · exact ⟨2, by omega, x - (a + b - 2) + 1, by simp only [tgArmLen]; omega, by
      show armIdx (a + b - 2) c (a + b + c - 3) (a + b + c - 2) (x - (a + b - 2) + 1) = x
      rw [armIdx_mid (by omega) (by omega)]; omega⟩

end

/-- The `t`-th of three arm functions. -/
def tgVert {W : Type} (p q r : ℕ → W) : ℕ → ℕ → W
  | 0 => p
  | 1 => q
  | _ => r

/-- **`H` is exactly the union of three internally disjoint paths.** -/
structure IsThetaArms {W : Type} (H : SimpleGraph W) (a b c : ℕ) (p q r : ℕ → W) : Prop where
  one_le_a : 1 ≤ a
  one_le_b : 1 ≤ b
  one_le_c : 1 ≤ c
  start : ∀ t, t < 3 → tgVert p q r t 0 = p 0
  finish : ∀ t, t < 3 → tgVert p q r t (tgArmLen a b c t) = p a
  adj : ∀ t, t < 3 → ∀ i, i < tgArmLen a b c t →
    H.Adj (tgVert p q r t i) (tgVert p q r t (i + 1))
  inj : ∀ t, t < 3 → ∀ i, i ≤ tgArmLen a b c t → ∀ j, j ≤ tgArmLen a b c t →
    tgVert p q r t i = tgVert p q r t j → i = j
  disj : ∀ t, t < 3 → ∀ t', t' < 3 → t ≠ t' → ∀ i, 0 < i → i < tgArmLen a b c t →
    ∀ j, 0 < j → j < tgArmLen a b c t' → tgVert p q r t i ≠ tgVert p q r t' j
  cover : ∀ w : W, ∃ t, t < 3 ∧ ∃ i, i ≤ tgArmLen a b c t ∧ tgVert p q r t i = w
  edges : ∀ u v : W, H.Adj u v → ∃ t, t < 3 ∧ ∃ i, i < tgArmLen a b c t ∧
    ((u = tgVert p q r t i ∧ v = tgVert p q r t (i + 1)) ∨
      (v = tgVert p q r t i ∧ u = tgVert p q r t (i + 1)))

/-- The vertex of `H` sitting at index `x` of the `thetaGen a b c` layout. -/
def armVertex {W : Type} (a b c : ℕ) (p q r : ℕ → W) (x : ℕ) : W :=
  if x = a + b + c - 2 then p a
  else if x = a + b + c - 3 then p 0
  else if x < a - 1 then p (x + 1)
  else if x < a + b - 2 then q (x - (a - 1) + 1)
  else r (x - (a + b - 2) + 1)

section Arms
variable {W : Type} {H : SimpleGraph W} {a b c : ℕ} {p q r : ℕ → W}

lemma armVertex_tgArm (h : IsThetaArms H a b c p q r) {t : ℕ} (ht : t < 3) {i : ℕ}
    (hi : i ≤ tgArmLen a b c t) :
    armVertex a b c p q r (tgArm a b c t i) = tgVert p q r t i := by
  have ha := h.one_le_a
  have hb := h.one_le_b
  have hc := h.one_le_c
  match t, ht with
  | 0, _ =>
    have hi' : i ≤ a := hi
    show armVertex a b c p q r (armIdx 0 a (a + b + c - 3) (a + b + c - 2) i) = p i
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [armIdx_zero]; unfold armVertex; rw [if_neg (by omega), if_pos rfl]
    by_cases hil : i < a
    · rw [armIdx_mid hi0 hil]; unfold armVertex
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    · rw [show i = a by omega, armIdx_len ha]; unfold armVertex; rw [if_pos rfl]
  | 1, _ =>
    have hi' : i ≤ b := hi
    show armVertex a b c p q r (armIdx (a - 1) b (a + b + c - 3) (a + b + c - 2) i) = q i
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [armIdx_zero]; unfold armVertex; rw [if_neg (by omega), if_pos rfl]
      exact (h.start 1 (by omega)).symm
    by_cases hil : i < b
    · rw [armIdx_mid hi0 hil]; unfold armVertex
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    · rw [show i = b by omega, armIdx_len hb]; unfold armVertex; rw [if_pos rfl]
      exact (h.finish 1 (by omega)).symm
  | 2, _ =>
    have hi' : i ≤ c := hi
    show armVertex a b c p q r (armIdx (a + b - 2) c (a + b + c - 3) (a + b + c - 2) i) = r i
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [armIdx_zero]; unfold armVertex; rw [if_neg (by omega), if_pos rfl]
      exact (h.start 2 (by omega)).symm
    by_cases hil : i < c
    · rw [armIdx_mid hi0 hil]; unfold armVertex
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      congr 1; omega
    · rw [show i = c by omega, armIdx_len hc]; unfold armVertex; rw [if_pos rfl]
      exact (h.finish 2 (by omega)).symm

lemma tgArm_zero {t : ℕ} (ht : t < 3) : tgArm a b c t 0 = a + b + c - 3 := by
  match t, ht with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

lemma tgArm_top (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) {t : ℕ} (ht : t < 3) :
    tgArm a b c t (tgArmLen a b c t) = a + b + c - 2 := by
  match t, ht with
  | 0, _ => exact armIdx_len ha
  | 1, _ => exact armIdx_len hb
  | 2, _ => exact armIdx_len hc

lemma thetaArms_len_pos (h : IsThetaArms H a b c p q r) {t : ℕ} (ht : t < 3) :
    1 ≤ tgArmLen a b c t := by
  match t, ht with
  | 0, _ => exact h.one_le_a
  | 1, _ => exact h.one_le_b
  | 2, _ => exact h.one_le_c

lemma thetaArms_start_ne (h : IsThetaArms H a b c p q r) : p 0 ≠ p a := by
  intro heq
  have h0 : (0 : ℕ) = a := h.inj 0 (by omega) 0 (Nat.zero_le _) a le_rfl heq
  have := h.one_le_a
  omega

lemma thetaArms_eq_start (h : IsThetaArms H a b c p q r) {t : ℕ} (ht : t < 3) {i : ℕ}
    (hi : i ≤ tgArmLen a b c t) (heq : tgVert p q r t i = p 0) : i = 0 :=
  h.inj t ht i hi 0 (Nat.zero_le _) (by rw [heq]; exact (h.start t ht).symm)

lemma thetaArms_eq_top (h : IsThetaArms H a b c p q r) {t : ℕ} (ht : t < 3) {i : ℕ}
    (hi : i ≤ tgArmLen a b c t) (heq : tgVert p q r t i = p a) : i = tgArmLen a b c t :=
  h.inj t ht i hi _ le_rfl (by rw [heq]; exact (h.finish t ht).symm)

/-- **Rigidity.** Two positions of the arms carrying the same vertex sit at the same index. -/
lemma thetaArms_rigid (h : IsThetaArms H a b c p q r) {t t' : ℕ} (ht : t < 3) (ht' : t' < 3)
    {i i' : ℕ} (hi : i ≤ tgArmLen a b c t) (hi' : i' ≤ tgArmLen a b c t')
    (heq : tgVert p q r t i = tgVert p q r t' i') :
    tgArm a b c t i = tgArm a b c t' i' := by
  have ha := h.one_le_a
  have hb := h.one_le_b
  have hc := h.one_le_c
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hz : i' = 0 := thetaArms_eq_start h ht' hi' (by rw [← heq]; exact h.start t ht)
    rw [hz, tgArm_zero ht, tgArm_zero ht']
  by_cases hitop : i = tgArmLen a b c t
  · subst hitop
    have hz : i' = tgArmLen a b c t' :=
      thetaArms_eq_top h ht' hi' (by rw [← heq]; exact h.finish t ht)
    rw [hz, tgArm_top ha hb hc ht, tgArm_top ha hb hc ht']
  -- `i` is interior, hence so is `i'`
  have hi0' : i' ≠ 0 := by
    intro hz
    refine absurd (thetaArms_eq_start h ht hi ?_) (by omega)
    rw [heq, hz]
    exact h.start t' ht'
  have hitop' : i' ≠ tgArmLen a b c t' := by
    intro hz
    refine absurd (thetaArms_eq_top h ht hi ?_) hitop
    rw [heq, hz]
    exact h.finish t' ht'
  by_cases htt : t = t'
  · subst htt
    rw [h.inj t ht i hi i' hi' heq]
  · exact absurd heq (h.disj t ht t' ht' htt i hi0 (by omega) i' (by omega) (by omega))

/-- The converse of `Monophilic.thetaArms_rigid`. -/
lemma thetaArms_rigid' (h : IsThetaArms H a b c p q r) {t t' : ℕ} (ht : t < 3) (ht' : t' < 3)
    {i i' : ℕ} (hi : i ≤ tgArmLen a b c t) (hi' : i' ≤ tgArmLen a b c t')
    (heq : tgArm a b c t i = tgArm a b c t' i') :
    tgVert p q r t i = tgVert p q r t' i' := by
  rw [← armVertex_tgArm h ht hi, ← armVertex_tgArm h ht' hi', heq]

/-- **An indexing in the `thetaGen` layout is an isomorphism onto `thetaGen`.** -/
theorem nonempty_iso_thetaGen_of_index {W : Type} {H : SimpleGraph W} {a b c : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (g : ℕ → W)
    (hinj : Set.InjOn g (Set.Iio (a + b + c - 1)))
    (hsurj : ∀ w, ∃ i, i < a + b + c - 1 ∧ g i = w)
    (hadj : ∀ x, x < a + b + c - 1 → ∀ y, y < a + b + c - 1 →
      (H.Adj (g x) (g y) ↔ (ThetaStep a b c x y ∨ ThetaStep a b c y x))) :
    Nonempty (H ≃g thetaGen a b c) := by
  have hbij : Function.Bijective (fun u : TGV a b c => g u.val) := by
    constructor
    · intro u v huv
      exact Fin.ext (hinj (Set.mem_Iio.mpr u.isLt) (Set.mem_Iio.mpr v.isLt) huv)
    · intro w
      obtain ⟨i, hi, rfl⟩ := hsurj w
      exact ⟨⟨i, hi⟩, rfl⟩
  refine ⟨SimpleGraph.Iso.symm ⟨Equiv.ofBijective _ hbij, ?_⟩⟩
  intro u v
  show H.Adj (g u.val) (g v.val) ↔ (thetaGen a b c).Adj u v
  rw [thetaGen_adj_iff ha hb hc, hadj u.val u.isLt v.val v.isLt]

/-- **A graph that is exactly the union of three internally disjoint paths of lengths `a`, `b`, `c`
joining two branch vertices is the theta graph `θ_{a,b,c}`.**

Classical, and the step **Rubin's theorem** (Erdős–Rubin–Taylor 1980, pp. 131–134) takes without
comment when it writes "`C₁ ∪ P₁ = θ_{a,b,c}`": a cycle `C₁` together with a path `P₁` joining two of
its vertices and otherwise disjoint from it *is* three internally disjoint paths — the two arcs of
`C₁` and `P₁` — between the two ends of `P₁`. Not novel; the content here is the identification of
the two encodings. See `Monophilic.nonempty_iso_thetaGen_of_paths` for the same statement with the
hypotheses spelt out one path at a time. -/
theorem nonempty_iso_thetaGen_of_arms (h : IsThetaArms H a b c p q r) :
    Nonempty (H ≃g thetaGen a b c) := by
  have ha := h.one_le_a
  have hb := h.one_le_b
  have hc := h.one_le_c
  refine nonempty_iso_thetaGen_of_index ha hb hc (armVertex a b c p q r) ?_ ?_ ?_
  · intro x hx y hy hxy
    simp only [Set.mem_Iio] at hx hy
    obtain ⟨t, ht, i, hi, rfl⟩ := tgArm_surj ha hb hc hx
    obtain ⟨t', ht', i', hi', rfl⟩ := tgArm_surj ha hb hc hy
    rw [armVertex_tgArm h ht hi, armVertex_tgArm h ht' hi'] at hxy
    exact thetaArms_rigid h ht ht' hi hi' hxy
  · intro w
    obtain ⟨t, ht, i, hi, rfl⟩ := h.cover w
    exact ⟨tgArm a b c t i, tgArm_lt ha hb hc ht hi, armVertex_tgArm h ht hi⟩
  · intro x hx y hy
    obtain ⟨t, ht, i, hi, rfl⟩ := tgArm_surj ha hb hc hx
    obtain ⟨t', ht', i', hi', rfl⟩ := tgArm_surj ha hb hc hy
    rw [armVertex_tgArm h ht hi, armVertex_tgArm h ht' hi']
    constructor
    · intro hAdj
      obtain ⟨s, hs, j, hj, hcase⟩ := h.edges _ _ hAdj
      rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨s, hs, j, hj, thetaArms_rigid h ht hs hi (le_of_lt hj) e1,
          thetaArms_rigid h ht' hs hi' (by omega) e2⟩
      · exact Or.inr ⟨s, hs, j, hj, thetaArms_rigid h ht' hs hi' (le_of_lt hj) e1,
          thetaArms_rigid h ht hs hi (by omega) e2⟩
    · rintro (⟨s, hs, j, hj, e1, e2⟩ | ⟨s, hs, j, hj, e1, e2⟩)
      · rw [thetaArms_rigid' h ht hs hi (le_of_lt hj) e1,
          thetaArms_rigid' h ht' hs hi' (by omega) e2]
        exact h.adj s hs j hj
      · rw [thetaArms_rigid' h ht' hs hi' (le_of_lt hj) e1,
          thetaArms_rigid' h ht hs hi (by omega) e2]
        exact (h.adj s hs j hj).symm

lemma arm_inj_of {W : Type} {x y : W} {p : ℕ → W} {a : ℕ} (ha : 1 ≤ a) (hxy : x ≠ y)
    (hp0 : p 0 = x) (hpa : p a = y)
    (hpin : ∀ i, 0 < i → i < a → p i ≠ x ∧ p i ≠ y)
    (hpinj : ∀ i, 0 < i → i < a → ∀ j, 0 < j → j < a → p i = p j → i = j) :
    ∀ i, i ≤ a → ∀ j, j ≤ a → p i = p j → i = j := by
  intro i hi j hj hij
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rfl
    rcases eq_or_lt_of_le hj with rfl | hjl
    · exact absurd (hp0 ▸ hpa ▸ hij) hxy
    · exact absurd (hp0 ▸ hij).symm (hpin j hj0 hjl).1
  rcases eq_or_lt_of_le hi with rfl | hil
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd (hp0 ▸ hpa ▸ hij.symm) hxy
    rcases eq_or_lt_of_le hj with rfl | hjl
    · rfl
    · exact absurd (hpa ▸ hij).symm (hpin j hj0 hjl).2
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd (hp0 ▸ hij) (hpin i hi0 hil).1
    rcases eq_or_lt_of_le hj with rfl | hjl
    · exact absurd (hpa ▸ hij) (hpin i hi0 hil).2
    · exact hpinj i hi0 hil j hj0 hjl hij

/-- **`C₁ ∪ P₁` is a theta graph**, with the hypotheses spelt out one path at a time.

`H` carries two distinct vertices `x`, `y` and three paths `p`, `q`, `r` from `x` to `y`, of lengths
`a`, `b`, `c`, each injective, with interiors avoiding `x` and `y` and pairwise disjoint; together
they cover every vertex of `H` and carry every edge of `H`. Then `H ≃g θ_{a,b,c}`.

Read for Rubin's step 4 with `p`, `q` the two arcs into which the two ends of `P₁` cut the cycle
`C₁`, and `r = P₁`: the hypotheses are then exactly "`P₁` joins two distinct nodes of `C₁`, is
internally disjoint from it, and `H` is `C₁ ∪ P₁` and nothing more".

Classical, and stated without proof in **Rubin's theorem** (Erdős–Rubin–Taylor 1980, pp. 131–134).
Not novel. -/
theorem nonempty_iso_thetaGen_of_paths {W : Type} {H : SimpleGraph W} {a b c : ℕ} {x y : W}
    {p q r : ℕ → W}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hxy : x ≠ y)
    (hp0 : p 0 = x) (hpa : p a = y) (hq0 : q 0 = x) (hqb : q b = y)
    (hr0 : r 0 = x) (hrc : r c = y)
    (hpadj : ∀ i, i < a → H.Adj (p i) (p (i + 1)))
    (hqadj : ∀ i, i < b → H.Adj (q i) (q (i + 1)))
    (hradj : ∀ i, i < c → H.Adj (r i) (r (i + 1)))
    (hpin : ∀ i, 0 < i → i < a → p i ≠ x ∧ p i ≠ y)
    (hqin : ∀ i, 0 < i → i < b → q i ≠ x ∧ q i ≠ y)
    (hrin : ∀ i, 0 < i → i < c → r i ≠ x ∧ r i ≠ y)
    (hpinj : ∀ i, 0 < i → i < a → ∀ j, 0 < j → j < a → p i = p j → i = j)
    (hqinj : ∀ i, 0 < i → i < b → ∀ j, 0 < j → j < b → q i = q j → i = j)
    (hrinj : ∀ i, 0 < i → i < c → ∀ j, 0 < j → j < c → r i = r j → i = j)
    (hpq : ∀ i, 0 < i → i < a → ∀ j, 0 < j → j < b → p i ≠ q j)
    (hpr : ∀ i, 0 < i → i < a → ∀ j, 0 < j → j < c → p i ≠ r j)
    (hqr : ∀ i, 0 < i → i < b → ∀ j, 0 < j → j < c → q i ≠ r j)
    (hcover : ∀ w : W, (∃ i, i ≤ a ∧ p i = w) ∨ (∃ i, i ≤ b ∧ q i = w) ∨ (∃ i, i ≤ c ∧ r i = w))
    (hedges : ∀ u v : W, H.Adj u v →
      (∃ i, i < a ∧ ((u = p i ∧ v = p (i + 1)) ∨ (v = p i ∧ u = p (i + 1)))) ∨
      (∃ i, i < b ∧ ((u = q i ∧ v = q (i + 1)) ∨ (v = q i ∧ u = q (i + 1)))) ∨
      (∃ i, i < c ∧ ((u = r i ∧ v = r (i + 1)) ∨ (v = r i ∧ u = r (i + 1))))) :
    Nonempty (H ≃g thetaGen a b c) := by
  refine nonempty_iso_thetaGen_of_arms (H := H) (a := a) (b := b) (c := c) (p := p) (q := q)
    (r := r) ?_
  refine ⟨ha, hb, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    match t, ht with
    | 0, _ => rfl
    | 1, _ => exact hq0.trans hp0.symm
    | 2, _ => exact hr0.trans hp0.symm
  · intro t ht
    match t, ht with
    | 0, _ => rfl
    | 1, _ => exact hqb.trans hpa.symm
    | 2, _ => exact hrc.trans hpa.symm
  · intro t ht
    match t, ht with
    | 0, _ => exact hpadj
    | 1, _ => exact hqadj
    | 2, _ => exact hradj
  · intro t ht
    match t, ht with
    | 0, _ => exact arm_inj_of ha hxy hp0 hpa hpin hpinj
    | 1, _ => exact arm_inj_of hb hxy hq0 hqb hqin hqinj
    | 2, _ => exact arm_inj_of hc hxy hr0 hrc hrin hrinj
  · intro t ht t' ht' htt
    match t, ht, t', ht' with
    | 0, _, 0, _ => exact absurd rfl htt
    | 0, _, 1, _ => exact fun i hi hia j hj hjb => hpq i hi hia j hj hjb
    | 0, _, 2, _ => exact fun i hi hia j hj hjc => hpr i hi hia j hj hjc
    | 1, _, 0, _ => exact fun i hi hib j hj hja e => hpq j hj hja i hi hib e.symm
    | 1, _, 1, _ => exact absurd rfl htt
    | 1, _, 2, _ => exact fun i hi hib j hj hjc => hqr i hi hib j hj hjc
    | 2, _, 0, _ => exact fun i hi hic j hj hja e => hpr j hj hja i hi hic e.symm
    | 2, _, 1, _ => exact fun i hi hic j hj hjb e => hqr j hj hjb i hi hic e.symm
    | 2, _, 2, _ => exact absurd rfl htt
  · intro w
    rcases hcover w with ⟨i, hi, hw⟩ | ⟨i, hi, hw⟩ | ⟨i, hi, hw⟩
    · exact ⟨0, by omega, i, hi, hw⟩
    · exact ⟨1, by omega, i, hi, hw⟩
    · exact ⟨2, by omega, i, hi, hw⟩
  · intro u v huv
    rcases hedges u v huv with ⟨i, hi, hcase⟩ | ⟨i, hi, hcase⟩ | ⟨i, hi, hcase⟩
    · exact ⟨0, by omega, i, hi, hcase⟩
    · exact ⟨1, by omega, i, hi, hcase⟩
    · exact ⟨2, by omega, i, hi, hcase⟩

end Arms
/-! ### The shape `(2, 2, 2m)`: `Monophilic.theta m`

Rubin's theorem names its theta family `θ_{2,2,2m}`, and this development builds that family
separately, as `Monophilic.theta m` — a path of length `2m` with two extra vertices, each joined to
both of its ends (`Monophilic.thetaOf`). The two models therefore have to be identified. Rather than
compare index formulas, `Monophilic.thetaOf k` is presented as three explicit arms of lengths `2`,
`2` and `k` and handed to `Monophilic.nonempty_iso_thetaGen_of_paths`. -/

/-- Index `0` of a path is `pathEnd`. -/
lemma pathAt_zero : ∀ k : ℕ, pathAt k 0 = pathEnd k
  | 0 => rfl
  | _ + 1 => rfl

/-- Index `k` of `pathG k` is `pathStart`. -/
lemma pathAt_self (k : ℕ) : pathAt k k = pathStart k := by
  have h := pathAt_pathNum k (pathStart k)
  rw [pathNum_pathStart k] at h
  exact h

section
variable (k : ℕ)

/-- The outer apex of `thetaOf k` is joined to the two ends of the path and to nothing else. -/
lemma thetaOf_adj_none_someSome (z : PathV k) :
    (thetaOf k).Adj none (some (some z)) ↔ (z = pathStart k ∨ z = pathEnd k) := by
  unfold thetaOf; simp

/-- The two apexes of `thetaOf k` are not joined to each other. -/
lemma thetaOf_not_adj_none_someNone : ¬ (thetaOf k).Adj none (some none) := by
  unfold thetaOf; simp

/-- The inner apex of `thetaOf k` is joined to the two ends of the path and to nothing else. -/
lemma thetaOf_adj_someNone_someSome (z : PathV k) :
    (thetaOf k).Adj (some none) (some (some z)) ↔ (z = pathStart k ∨ z = pathEnd k) := by
  unfold thetaOf thetaBaseOf; simp

/-- Along the path, `thetaOf k` has exactly the edges of `pathG k`. -/
lemma thetaOf_adj_someSome (z z' : PathV k) :
    (thetaOf k).Adj (some (some z)) (some (some z')) ↔ (pathG k).Adj z z' := by
  unfold thetaOf thetaBaseOf; simp

end

/-- The first length-`2` arm of `thetaOf k`: through the inner apex. -/
def thArmA (k : ℕ) : ℕ → Option (Option (PathV k))
  | 0 => some (some (pathStart k))
  | 1 => some none
  | _ => some (some (pathEnd k))

/-- The second length-`2` arm of `thetaOf k`: through the outer apex. -/
def thArmB (k : ℕ) : ℕ → Option (Option (PathV k))
  | 0 => some (some (pathStart k))
  | 1 => none
  | _ => some (some (pathEnd k))

/-- The long arm of `thetaOf k`: the path itself, indexed from `pathStart`. -/
def thArmC (k : ℕ) (i : ℕ) : Option (Option (PathV k)) := some (some (pathAt k (k - i)))

/-- **`Monophilic.thetaOf k` is `θ_{2,2,k}`.** The path of length `k` with two extra vertices each
joined to both of its ends, presented as three arms and identified with the general model.

Bookkeeping between two encodings of the same graph, not mathematics; the graph itself is the
`θ_{2,2,2m}` of **Rubin's theorem** (Erdős–Rubin–Taylor 1980, pp. 131–134) when `k` is even. -/
theorem nonempty_iso_thetaOf_thetaGen (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (thetaOf k ≃g thetaGen 2 2 k) := by
  have hne : (pathStart k) ≠ (pathEnd k) := by
    intro h
    have := pathNum_pathStart k
    rw [h, pathNum_pathEnd] at this
    omega
  refine nonempty_iso_thetaGen_of_paths (H := thetaOf k) (x := some (some (pathStart k)))
    (y := some (some (pathEnd k))) (p := thArmA k) (q := thArmB k) (r := thArmC k)
    (by omega) (by omega) hk (by simpa using hne) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- `thArmC k 0 = x`
  · show some (some (pathAt k (k - 0))) = _
    rw [Nat.sub_zero, pathAt_self]
  -- `thArmC k k = y`
  · show some (some (pathAt k (k - k))) = _
    rw [Nat.sub_self, pathAt_zero]
  -- adjacency along the first short arm
  · intro i hi
    match i, hi with
    | 0, _ => exact ((thetaOf_adj_someNone_someSome k _).mpr (Or.inl rfl)).symm
    | 1, _ => exact (thetaOf_adj_someNone_someSome k _).mpr (Or.inr rfl)
  -- adjacency along the second short arm
  · intro i hi
    match i, hi with
    | 0, _ => exact ((thetaOf_adj_none_someSome k _).mpr (Or.inl rfl)).symm
    | 1, _ => exact (thetaOf_adj_none_someSome k _).mpr (Or.inr rfl)
  -- adjacency along the long arm
  · intro i hi
    show (thetaOf k).Adj (some (some (pathAt k (k - i)))) (some (some (pathAt k (k - (i + 1)))))
    rw [thetaOf_adj_someSome, pathG_adj_num, pathNum_pathAt k _ (by omega),
      pathNum_pathAt k _ (by omega)]
    omega
  -- interiors of the arms are not the branch vertices
  · intro i hi0 hi
    match i, hi with
    | 1, _ => exact ⟨by simp [thArmA], by simp [thArmA]⟩
  · intro i hi0 hi
    match i, hi with
    | 1, _ => exact ⟨by simp [thArmB], by simp [thArmB]⟩
  · intro i hi0 hi
    refine ⟨fun hEq => ?_, fun hEq => ?_⟩
    · have h1 : pathAt k (k - i) = pathStart k := by simpa [thArmC] using hEq
      have := pathNum_pathAt k (k - i) (by omega)
      rw [h1, pathNum_pathStart] at this
      omega
    · have h1 : pathAt k (k - i) = pathEnd k := by simpa [thArmC] using hEq
      have := pathNum_pathAt k (k - i) (by omega)
      rw [h1, pathNum_pathEnd] at this
      omega
  -- the arms are injective on their interiors
  · intro i hi0 hi j hj0 hj _
    omega
  · intro i hi0 hi j hj0 hj _
    omega
  · intro i hi0 hi j hj0 hj hEq
    have h1 : pathAt k (k - i) = pathAt k (k - j) := by simpa [thArmC] using hEq
    have e1 := pathNum_pathAt k (k - i) (by omega)
    have e2 := pathNum_pathAt k (k - j) (by omega)
    rw [h1, e2] at e1
    omega
  -- the interiors are pairwise disjoint
  · intro i hi0 hi j hj0 hj
    match i, hi, j, hj with
    | 1, _, 1, _ => simp [thArmA, thArmB]
  · intro i hi0 hi j hj0 hj
    match i, hi with
    | 1, _ => simp [thArmA, thArmC]
  · intro i hi0 hi j hj0 hj
    match i, hi with
    | 1, _ => simp [thArmB, thArmC]
  -- the arms cover every vertex
  · intro w
    match w with
    | none => exact Or.inr (Or.inl ⟨1, by omega, rfl⟩)
    | some none => exact Or.inl ⟨1, by omega, rfl⟩
    | some (some z) =>
        refine Or.inr (Or.inr ⟨k - pathNum k z, by omega, ?_⟩)
        show some (some (pathAt k (k - (k - pathNum k z)))) = some (some z)
        rw [show k - (k - pathNum k z) = pathNum k z from by have := pathNum_le k z; omega,
          pathAt_pathNum]
  -- and carry every edge
  · intro u v huv
    match u, v with
    | none, none => exact absurd huv (by unfold thetaOf; simp)
    | none, some none => exact absurd huv (thetaOf_not_adj_none_someNone k)
    | some none, none => exact absurd huv (fun h => thetaOf_not_adj_none_someNone k h.symm)
    | some none, some none => exact absurd huv (by unfold thetaOf; simp)
    | none, some (some z) =>
        rcases (thetaOf_adj_none_someSome k z).mp huv with rfl | rfl
        · exact Or.inr (Or.inl ⟨0, by omega, Or.inr ⟨rfl, rfl⟩⟩)
        · exact Or.inr (Or.inl ⟨1, by omega, Or.inl ⟨rfl, rfl⟩⟩)
    | some (some z), none =>
        rcases (thetaOf_adj_none_someSome k z).mp huv.symm with rfl | rfl
        · exact Or.inr (Or.inl ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩)
        · exact Or.inr (Or.inl ⟨1, by omega, Or.inr ⟨rfl, rfl⟩⟩)
    | some none, some (some z) =>
        rcases (thetaOf_adj_someNone_someSome k z).mp huv with rfl | rfl
        · exact Or.inl ⟨0, by omega, Or.inr ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨1, by omega, Or.inl ⟨rfl, rfl⟩⟩
    | some (some z), some none =>
        rcases (thetaOf_adj_someNone_someSome k z).mp huv.symm with rfl | rfl
        · exact Or.inl ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨1, by omega, Or.inr ⟨rfl, rfl⟩⟩
    | some (some z), some (some z') =>
        have hz := pathNum_le k z
        have hz' := pathNum_le k z'
        rcases (pathG_adj_num k z z').mp ((thetaOf_adj_someSome k z z').mp huv) with h | h
        · refine Or.inr (Or.inr ⟨k - pathNum k z', by omega, Or.inr ⟨?_, ?_⟩⟩)
          · show some (some z') = some (some (pathAt k (k - (k - pathNum k z'))))
            rw [show k - (k - pathNum k z') = pathNum k z' from by omega, pathAt_pathNum]
          · show some (some z) = some (some (pathAt k (k - (k - pathNum k z' + 1))))
            rw [show k - (k - pathNum k z' + 1) = pathNum k z from by omega, pathAt_pathNum]
        · refine Or.inr (Or.inr ⟨k - pathNum k z, by omega, Or.inl ⟨?_, ?_⟩⟩)
          · show some (some z) = some (some (pathAt k (k - (k - pathNum k z))))
            rw [show k - (k - pathNum k z) = pathNum k z from by omega, pathAt_pathNum]
          · show some (some z') = some (some (pathAt k (k - (k - pathNum k z + 1))))
            rw [show k - (k - pathNum k z + 1) = pathNum k z' from by omega, pathAt_pathNum]

/-- **`Monophilic.theta m` is `θ_{2,2,2m}` on the general model.** Bookkeeping between the two
encodings; the family is **Rubin's** (Erdős–Rubin–Taylor 1980, pp. 131–134). -/
theorem nonempty_iso_theta_thetaGen (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (theta m ≃g thetaGen 2 2 (2 * m)) :=
  nonempty_iso_thetaOf_thetaGen (2 * m) (by omega)

/-- **The `(2, 2, 2m)` case.** A graph isomorphic to `θ_{2,2,2m}` on the general model is
isomorphic to `Monophilic.theta m`, which is the form `Monophilic.CoreIsTheta` — and hence
`Monophilic.RubinTheorem` — asks for. Bookkeeping; the family is **Rubin's**
(Erdős–Rubin–Taylor 1980, pp. 131–134). -/
theorem nonempty_iso_theta_of_iso_thetaGen {W : Type} {H : SimpleGraph W} {m : ℕ} (hm : 1 ≤ m)
    (h : Nonempty (H ≃g thetaGen 2 2 (2 * m))) : Nonempty (H ≃g theta m) :=
  ⟨h.some.trans (nonempty_iso_theta_thetaGen m hm).some.symm⟩

/-! ### Sanity checks

The index conventions are the part of this file that a type error would not catch, so they are
checked numerically before anything is proved from them. -/

section Guards

-- `closePath k` is the cycle on `k + 1` vertices, and it is `2`-regular for `k ≥ 2`
#guard Fintype.card (PathV 4) = 5
#guard ((univ : Finset (PathV 4)).filter fun v => (closePath 4).degree v = 2).card = 5
#guard ((univ : Finset (PathV 5)).filter fun v => (closePath 5).degree v = 2).card = 6
#guard (closePath 4).edgeFinset.card = 5

-- `pathG k` has exactly two vertices of degree one, and `k - 1` of degree two
#guard ((univ : Finset (PathV 4)).filter fun v => (pathG 4).degree v = 1).card = 2
#guard ((univ : Finset (PathV 4)).filter fun v => (pathG 4).degree v = 2).card = 3

-- `pathNum` numbers `pathEnd` by `0` and `pathStart` by `k`, and `pathAt` inverts it
#guard [0, 1, 2, 3, 4, 5].all fun k => pathNum k (pathEnd k) == 0
#guard pathNum 0 (pathStart 0) = 0
#guard pathNum 1 (pathStart 1) = 1
#guard pathNum 5 (pathStart 5) = 5
#guard [0, 1, 2, 3, 4, 5].all fun k => (List.range (k + 1)).all fun i => pathNum k (pathAt k i) == i
#guard (univ : Finset (PathV 5)).image (pathNum 5) = Finset.range 6

-- the two adjacency characterizations, at the sizes where an off-by-one would show
#guard decide (∀ a b : PathV 4,
  (pathG 4).Adj a b ↔ (pathNum 4 a + 1 = pathNum 4 b ∨ pathNum 4 b + 1 = pathNum 4 a))
#guard decide (∀ a b : PathV 4, (closePath 4).Adj a b ↔
  (pathNum 4 a + 1 = pathNum 4 b ∨ pathNum 4 b + 1 = pathNum 4 a ∨
    (pathNum 4 a = 0 ∧ pathNum 4 b = 4) ∨ (pathNum 4 b = 0 ∧ pathNum 4 a = 4)))
#guard decide (∀ a b : PathV 5, (closePath 5).Adj a b ↔
  (pathNum 5 a + 1 = pathNum 5 b ∨ pathNum 5 b + 1 = pathNum 5 a ∨
    (pathNum 5 a = 0 ∧ pathNum 5 b = 5) ∨ (pathNum 5 b = 0 ∧ pathNum 5 a = 5)))

-- a pendant tower over the one-vertex graph really does have a vertex of degree one to delete
#guard ((univ : Finset (TowerV (PathV 0) 2)).filter fun v =>
  (SimpleGraph.pendantTower (pathG 0) 2 ((PUnit.unit, pathEnd 0), pathEnd 1)).degree v = 1).card = 2

/-- `Monophilic.ThetaStep` is a bounded existential, hence decidable — which is what lets the
layout of `thetaGen` be machine-checked below rather than merely asserted. -/
instance instDecidableThetaStep (a b c x y : ℕ) : Decidable (ThetaStep a b c x y) := by
  unfold ThetaStep
  infer_instance

-- the three arms of `θ_{3,4,5}`, in the layout `thetaGen` actually uses: the branch vertices are
-- the last two indices `9` and `10`, and the interiors partition `0, …, 8` in arm order
#guard ((List.range 4).map (tgArm 3 4 5 0)) = [9, 0, 1, 10]
#guard ((List.range 5).map (tgArm 3 4 5 1)) = [9, 2, 3, 4, 10]
#guard ((List.range 6).map (tgArm 3 4 5 2)) = [9, 5, 6, 7, 8, 10]
#guard ((List.range 2).map (tgArm 1 2 2 0)) = [2, 3]
#guard ((List.range 3).map (tgArm 2 2 2 1)) = [3, 1, 4]

-- `Monophilic.thetaGen_adj_iff`, checked at every shape with `1 ≤ a, b, c ≤ 4`
#guard [1, 2, 3, 4].all fun a => [1, 2, 3, 4].all fun b => [1, 2, 3, 4].all fun c =>
  decide (∀ u v : TGV a b c,
    ((thetaGen a b c).Adj u v ↔ (ThetaStep a b c u.val v.val ∨ ThetaStep a b c v.val u.val)))

-- and at the two shapes the theta case of Rubin's argument actually produces
#guard decide (∀ u v : TGV 2 2 6,
  ((thetaGen 2 2 6).Adj u v ↔ (ThetaStep 2 2 6 u.val v.val ∨ ThetaStep 2 2 6 v.val u.val)))
#guard decide (∀ u v : TGV 3 4 5,
  ((thetaGen 3 4 5).Adj u v ↔ (ThetaStep 3 4 5 u.val v.val ∨ ThetaStep 3 4 5 v.val u.val)))


-- `thetaOf k` and `thetaGen 2 2 k` really are the same graph
#guard Fintype.card (Option (Option (PathV 4))) = Fintype.card (TGV 2 2 4)
#guard (thetaOf 4).edgeFinset.card = (thetaGen 2 2 4).edgeFinset.card
#guard (thetaOf 4).colConst 3 = (thetaGen 2 2 4).colConst 3
#guard (thetaOf 6).colConst 3 = (thetaGen 2 2 6).colConst 3
#guard [thArmA 4 0, thArmA 4 1, thArmA 4 2] =
  [some (some (pathStart 4)), some none, some (some (pathEnd 4))]
#guard (List.range 5).map (fun i => pathNum 4 (pathAt 4 (4 - i))) = [4, 3, 2, 1, 0]

end Guards

#print axioms addPendantIso
#print axioms complSingletonEquiv
#print axioms isoAddPendantOfDegreeOne
#print axioms hasCore
#print axioms pathG_adj_num
#print axioms closePath_adj_num
#print axioms adj_eq_of_degree_two
#print axioms mem_of_walk
#print axioms nonempty_iso_closePath_of_index
#print axioms exists_iso_closePath_of_two_regular
#print axioms armStepB_iff_armIdx
#print axioms thetaGen_adj_iff
#print axioms tgArm_surj
#print axioms armVertex_tgArm
#print axioms thetaArms_rigid
#print axioms nonempty_iso_thetaGen_of_index
#print axioms nonempty_iso_thetaGen_of_arms
#print axioms nonempty_iso_thetaGen_of_paths
#print axioms nonempty_iso_thetaOf_thetaGen
#print axioms nonempty_iso_theta_thetaGen
#print axioms nonempty_iso_theta_of_iso_thetaGen

end Monophilic
