/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Iso
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lemma 1 of Kirov–Naimi: coning off a clique

Let `G` be enumeratively chromatic-choosable at `n`, and let `v₁, …, v_k` induce a complete subgraph
of `G`. Let `G'` be obtained from `G` by adding one new vertex joined to `v₁, …, v_k`. Then `G'` is
enumeratively chromatic-choosable at `n`. This is Lemma 1 of Kirov–Naimi, and it is the engine
behind the Kostochka–Sidorenko theorem (a graph with a simplicial elimination ordering is
enumeratively chromatic-choosable at `n` for every `n`).

The enlarged graph is modelled on `Option V`, with `none` playing the role of the new apex; see
`SimpleGraph.coneOn`. The proof is a counting argument: a coloring of the cone is a coloring `f` of
`G` together with a color for the apex avoiding `f(K)`, so the apex contributes a factor
`|M(none) \ f(K)|`. For a constant list of size `n` and a clique `K` this factor is *exactly*
`n - |K|` for every `f`, whereas for a general `n`-list assignment it is only *at least* `n - |K|`.
Comparing the two gives Lemma 1.

## Main results

* `SimpleGraph.coneOn` : `G` with a new vertex joined to the vertices of `K`
* `SimpleGraph.col_coneOn` : `col(coneOn G K, M) = ∑ f, |M(none) \ f(K)|`, summed over the colorings
  `f` of `G` from the restricted lists (no clique hypothesis needed)
* `SimpleGraph.colConst_coneOn` : `col(coneOn G K, n) = (n - |K|) * col(G, n)` for a clique `K`
* `SimpleGraph.mul_col_le_col_coneOn` : `(n - |K|) * col(G, M ∘ some) ≤ col(coneOn G K, M)`
* `SimpleGraph.ECCAt.coneOn` : **Lemma 1**
* `SimpleGraph.ecc_top` : complete graphs are enumeratively chromatic-choosable at `n` for every `n`
-/

open Finset

namespace SimpleGraph

/-! ### The cone over a set of vertices -/

section Def

variable {V : Type*}

/-- The adjacency relation of `SimpleGraph.coneOn`: the vertices of `V`, embedded as `some`, keep
the adjacencies they had in `G`, and the new apex `none` is adjacent to exactly the members of
`K`. -/
def coneAdj (G : SimpleGraph V) (K : Finset V) : Option V → Option V → Prop
  | some a, some b => G.Adj a b
  | none, some b => b ∈ K
  | some a, none => a ∈ K
  | none, none => False

/-- **The cone over `K`.** `coneOn G K` is the graph on `Option V` obtained from `G` by adding one
new vertex `none` joined to precisely the vertices in `K`.

When `K` is a clique this is the "add a simplicial vertex" operation of Kirov–Naimi, Lemma 1. -/
def coneOn (G : SimpleGraph V) (K : Finset V) : SimpleGraph (Option V) where
  Adj := coneAdj G K
  symm := ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact h.ne rfl⟩

variable (G : SimpleGraph V) (K : Finset V)

@[simp] lemma coneOn_adj_some_some (a b : V) :
    (coneOn G K).Adj (some a) (some b) ↔ G.Adj a b := Iff.rfl

@[simp] lemma coneOn_adj_none_some (b : V) :
    (coneOn G K).Adj none (some b) ↔ b ∈ K := Iff.rfl

@[simp] lemma coneOn_adj_some_none (a : V) :
    (coneOn G K).Adj (some a) none ↔ a ∈ K := Iff.rfl

@[simp] lemma coneOn_adj_none_none : ¬ (coneOn G K).Adj none none := id

/-- Adjacency in `coneAdj G K` is decidable as soon as adjacency in `G` and membership in `K`
are. -/
instance coneAdj.instDecidableRel [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (coneAdj G K)
  | some a, some b => inferInstanceAs (Decidable (G.Adj a b))
  | none, some b => inferInstanceAs (Decidable (b ∈ K))
  | some a, none => inferInstanceAs (Decidable (a ∈ K))
  | none, none => inferInstanceAs (Decidable False)

/-- Adjacency in the cone is decidable. -/
instance coneOn.instDecidableRel [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (coneOn G K).Adj := coneAdj.instDecidableRel G K

end Def

/-! ### Counting the extensions of a coloring

A coloring of `coneOn G K` restricts to a coloring of `G`, and the fibre of this restriction map
over a coloring `f` is indexed by the colors available to the apex that `f` does not already use
on `K`. -/

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {K : Finset V}

/-- Restricting a coloring of `coneOn G K` to the old vertices gives a coloring of `G` from the
restricted list assignment `M ∘ some`. -/
theorem comp_some_mem_colorings {M : ListAssignment (Option V)} {F : Option V → ℕ}
    (hF : F ∈ (coneOn G K).colorings M) : F ∘ some ∈ G.colorings (M ∘ some) := by
  rw [mem_colorings] at hF ⊢
  refine ⟨fun v => hF.1 (some v), ?_⟩
  intro v w hvw
  exact hF.2 ((coneOn_adj_some_some G K v w).mpr hvw)

/-- **The fibre count.** The colorings of `coneOn G K` from `M` restricting to a fixed coloring `f`
of `G` correspond to the colors of the apex list `M none` that `f` does not use on `K`. -/
theorem card_filter_comp_some {M : ListAssignment (Option V)} {f : V → ℕ}
    (hf : f ∈ G.colorings (M ∘ some)) :
    (((coneOn G K).colorings M).filter (fun F => F ∘ some = f)).card
      = (M none \ K.image f).card := by
  rw [mem_colorings] at hf
  refine Finset.card_nbij' (fun F => F none) (fun c o => o.elim c f) ?_ ?_ ?_ ?_
  · -- the apex color of an extension avoids the colors used on `K`
    intro F hF
    rw [Finset.mem_coe, Finset.mem_filter, mem_colorings] at hF
    obtain ⟨⟨hmem, hproper⟩, hres⟩ := hF
    refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hmem none, ?_⟩)
    intro hcon
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hcon
    have hfa' : f a = F none := hfa
    exact hproper ((coneOn_adj_none_some G K a).mpr ha)
      (hfa'.symm.trans (congrFun hres a).symm)
  · -- conversely, any such color extends `f`
    intro c hc
    rw [Finset.mem_coe, Finset.mem_sdiff] at hc
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_colorings.mpr ⟨?_, ?_⟩, rfl⟩)
    · rintro (_ | v)
      · exact hc.1
      · exact hf.1 v
    · rintro (_ | a) (_ | b) hadj
      · exact absurd hadj (coneOn_adj_none_none G K)
      · intro hcon
        exact hc.2 (Finset.mem_image.mpr
          ⟨b, (coneOn_adj_none_some G K b).mp hadj, hcon.symm⟩)
      · intro hcon
        exact hc.2 (Finset.mem_image.mpr
          ⟨a, (coneOn_adj_some_none G K a).mp hadj, hcon⟩)
      · exact hf.2 ((coneOn_adj_some_some G K a b).mp hadj)
  · intro F hF
    rw [Finset.mem_coe, Finset.mem_filter] at hF
    funext o
    cases o with
    | none => rfl
    | some v => exact (congrFun hF.2 v).symm
  · intro c _
    rfl

/-- **The extension count** (`col` of a cone). Summing the fibre count over all colorings of `G`
from the restricted lists computes `col` of the cone. No hypothesis on `K` is needed here. -/
theorem col_coneOn (M : ListAssignment (Option V)) :
    (coneOn G K).col M = ∑ f ∈ G.colorings (M ∘ some), (M none \ K.image f).card := by
  rw [col, Finset.card_eq_sum_card_fiberwise (f := fun F => F ∘ some)
    (t := G.colorings (M ∘ some)) (fun _ hF => comp_some_mem_colorings hF)]
  exact Finset.sum_congr rfl fun _ hf => card_filter_comp_some hf

/-! ### Constant lists: the count is exactly `(n - |K|) * col(G, n)` -/

/-- A proper coloring is injective on a clique. -/
theorem injOn_of_isClique {L : ListAssignment V} {f : V → ℕ} (hK : G.IsClique (K : Set V))
    (hf : f ∈ G.colorings L) : Set.InjOn f (K : Set V) := by
  intro a ha b hb hab
  by_contra hne
  exact isProperColoring_of_mem_colorings hf (hK ha hb hne) hab

/-- **Constant lists give equality.** Coning off a clique `K` multiplies the number of colorings
from the constant list of size `n` by exactly `n - |K|`.

Truncated subtraction is harmless: if `|K| ≥ n` then no proper coloring of `G` from `range n` can
be injective on `K`, so `col(G, n) = 0` and both sides vanish. The proof below does not need to
split into cases — for *every* coloring `f` occurring in the sum, `f(K) ⊆ range n` has exactly
`|K|` elements, which already forces `|K| ≤ n`. -/
theorem colConst_coneOn (hK : G.IsClique (K : Set V)) (n : ℕ) :
    (coneOn G K).colConst n = (n - K.card) * G.colConst n := by
  rw [colConst, col_coneOn]
  have key : ∀ f ∈ G.colorings (constList (Option V) n ∘ some),
      (constList (Option V) n none \ K.image f).card = n - K.card := by
    intro f hf
    have hsub : K.image f ⊆ range n := by
      intro c hc
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hc
      exact mem_list_of_mem_colorings hf v
    rw [show constList (Option V) n none = range n from rfl,
      Finset.card_sdiff_of_subset hsub, Finset.card_range,
      Finset.card_image_of_injOn (injOn_of_isClique hK hf)]
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ### Arbitrary lists: the count is at least `(n - |K|) * col(G, ·)` -/

/-- **Lower bound for arbitrary lists.** For an `n`-list assignment `M` on the cone, the apex has
at least `n - |K|` free colors above every coloring of `G`. Note that no clique hypothesis is
needed: `|f(K)| ≤ |K|` always. -/
theorem mul_col_le_col_coneOn {M : ListAssignment (Option V)} {n : ℕ}
    (hM : IsNListAssignment M n) :
    (n - K.card) * G.col (M ∘ some) ≤ (coneOn G K).col M := by
  rw [col_coneOn]
  have hconst : (n - K.card) * G.col (M ∘ some)
      = ∑ _f ∈ G.colorings (M ∘ some), (n - K.card) := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rfl
  rw [hconst]
  refine Finset.sum_le_sum fun f _ => ?_
  have h1 : (K.image f).card ≤ K.card := Finset.card_image_le
  have h2 : (M none).card = n := hM none
  have h3 : (M none).card - (K.image f).card ≤ (M none \ K.image f).card :=
    Finset.le_card_sdiff _ _
  omega

/-! ### Lemma 1 -/

/-- **Kirov–Naimi, Lemma 1.** If `G` is enumeratively chromatic-choosable at `n` and `K` is a
clique of `G`, then the graph obtained from `G` by adding a new vertex joined to `K` is
enumeratively chromatic-choosable at `n`. -/
theorem ECCAt.coneOn (hK : G.IsClique (K : Set V)) {n : ℕ} (hG : G.ECCAt n) :
    (SimpleGraph.coneOn G K).ECCAt n := by
  intro M hM
  rw [colConst_coneOn hK]
  exact le_trans (Nat.mul_le_mul le_rfl (hG (M ∘ some) fun v => hM (some v)))
    (mul_col_le_col_coneOn hM)

end Counting

/-! ### Corollary: complete graphs are enumeratively chromatic-choosable at `n` -/

section Complete

/-- A graph on an empty vertex type is enumeratively chromatic-choosable at `n` for every `n`:
from any list assignment there is exactly one coloring, the empty function. This is the base case
of the induction below. -/
theorem ecc_of_isEmpty {V : Type*} [Fintype V] [DecidableEq V] [IsEmpty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : G.ECCAt n := by
  intro L _
  have h1 : G.colConst n ≤ 1 := by
    rw [colConst, col]
    exact Finset.card_le_one.mpr fun _ _ _ _ => funext fun v => isEmptyElim v
  have h2 : 0 < G.col L := by
    rw [col_pos_iff]
    refine ⟨fun _ => 0, mem_colorings.mpr ⟨fun v => isEmptyElim v, ?_⟩⟩
    intro v _ _
    exact isEmptyElim v
  omega

/-- Coning off *all* of a complete graph gives a complete graph again. -/
lemma coneOn_top_univ_adj {V : Type*} [Fintype V] (x y : Option V) :
    (coneOn (⊤ : SimpleGraph V) univ).Adj x y ↔ x ≠ y := by
  cases x <;> cases y <;> simp

/-- The complete graph on `Fin (m + 1)` is isomorphic to the cone over the complete graph on
`Fin m` with apex joined to every vertex. -/
def topIsoConeOnTop (m : ℕ) :
    (⊤ : SimpleGraph (Fin (m + 1))) ≃g coneOn (⊤ : SimpleGraph (Fin m)) univ where
  toEquiv := finSuccEquiv m
  map_rel_iff' := by
    intro a b
    rw [coneOn_top_univ_adj]
    simp

/-- Any complete graph is isomorphic to a complete graph on `Fin _`. -/
noncomputable def topIsoTopFin (V : Type*) [Fintype V] :
    (⊤ : SimpleGraph V) ≃g (⊤ : SimpleGraph (Fin (Fintype.card V))) where
  toEquiv := Fintype.equivFin V
  map_rel_iff' := by
    intro a b
    simp

/-- **Complete graphs on `Fin m` are enumeratively chromatic-choosable at `n`, for all `m` and
`n`.** The induction step is Lemma 1 applied to the clique consisting of all the old vertices. -/
theorem ecc_top_fin (m n : ℕ) : (⊤ : SimpleGraph (Fin m)).ECCAt n := by
  induction m with
  | zero => exact ecc_of_isEmpty _ n
  | succ m ih =>
    have hK : (⊤ : SimpleGraph (Fin m)).IsClique ((univ : Finset (Fin m)) : Set (Fin m)) := by
      intro a _ b _ hab
      exact hab
    exact (ecc_iso (topIsoConeOnTop m) n).mpr (ECCAt.coneOn hK ih)

/-- **Complete graphs are enumeratively chromatic-choosable at `n` for every `n`.** -/
theorem ecc_top (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) :
    (⊤ : SimpleGraph V).ECCAt n :=
  (ecc_iso (topIsoTopFin V) n).mpr (ecc_top_fin _ n)

end Complete

end SimpleGraph
