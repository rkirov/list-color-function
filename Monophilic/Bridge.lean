/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Rename
import Monophilic.Sum

/-!
# Bridged unions of graphs, and Lemma 2 of Kirov–Naimi

Kirov–Naimi, *List coloring and `n`-monophilic graphs* (arXiv:1004.5183), Lemma 2 reads:

> Let `G₁` and `G₂` be disjoint subgraphs of a graph `G`, with `vᵢ` a vertex of `Gᵢ`, and
> `G = G₁ ∪ G₂ + v₁v₂`. Let `L` be a list assignment for `G`. Then there is a list assignment `L'`
> with `|L'(v)| = |L(v)|` for every `v`, with `L'(v₁) ⊆ L'(v₂)` or `L'(v₂) ⊆ L'(v₁)`, and
> `col(G, L') ≤ col(G, L)`.

The graph `G` of the statement is modelled here as `bridge G H v₀ w₀`, the disjoint union `G ⊕g H`
with one extra edge joining `Sum.inl v₀` to `Sum.inr w₀`.

The proof has two halves. First, cutting along the bridge decomposes the count: a coloring of
`bridge G H v₀ w₀` giving color `c` to `v₀` is exactly a pair consisting of a coloring of `G`
sending `v₀ ↦ c` and a coloring of `H` sending `w₀` to *anything but* `c`. This motivates
`colAvoid`, the companion of `colFix` counting colorings that avoid a prescribed color at a vertex.

Second, if some `c₁ ∈ L(v₁) \ L(v₂)` and some `c₂ ∈ L(v₂) \ L(v₁)` exist, applying the transposition
`(c₁ c₂)` to every list on the `H` side produces `L'` with the same list sizes and
`col(G, L') ≤ col(G, L)`; this is the paper's equation (1), proved here in the `ℕ`-subtraction-free
form `col(G, L') + col(G, L, v₁, c₁) · col(H, L, v₂, c₂) = col(G, L)`. The swap strictly decreases
`|L(v₁) \ L(v₂)|`, so iterating terminates with the two lists nested.

## Main results

* `SimpleGraph.bridge` : the disjoint union plus one bridging edge
* `SimpleGraph.colAvoid` and `SimpleGraph.colAvoid_add_colFix` : counting colorings that avoid a
  color at a vertex
* `SimpleGraph.colFix_bridge`, `SimpleGraph.col_bridge` : cutting along the bridge
* `SimpleGraph.swapRight` : the transposition applied to the lists on one side of the bridge
* `SimpleGraph.col_swapRight_add` : the paper's equation (1)
* `SimpleGraph.col_swapRight_le`, `SimpleGraph.col_swapRight_lt` : the swap does not increase the
  number of colorings, and strictly decreases it under the paper's "moreover" hypothesis
* `SimpleGraph.card_sdiff_swapRight_lt` : the swap strictly decreases the termination measure
* `SimpleGraph.exists_nested_of_bridge` : **Lemma 2**
-/

open Finset

namespace SimpleGraph

/-! ### Avoiding a prescribed color at a vertex

`colFix G L v c` counts the colorings sending `v ↦ c`; `colAvoid G L v c` counts the complementary
family. We work with the additive identity `colAvoid + colFix = col` throughout, so that no
truncated `ℕ`-subtraction ever appears. -/

section Avoid

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `colAvoid G L v c`: the number of colorings of `G` from `L` that do **not** give the color `c`
to the vertex `v`. This is the complement of `SimpleGraph.colFix` inside `SimpleGraph.colorings`. -/
def colAvoid (G : SimpleGraph V) [DecidableRel G.Adj] (L : ListAssignment V) (v : V) (c : ℕ) : ℕ :=
  ((G.colorings L).filter fun f => f v ≠ c).card

/-- Every coloring either gives `c` to `v` or does not: `colAvoid` and `colFix` add up to `col`.
This is the subtraction-free form of `colAvoid = col - colFix`. -/
theorem colAvoid_add_colFix (L : ListAssignment V) (v : V) (c : ℕ) :
    G.colAvoid L v c + G.colFix L v c = G.col L := by
  rw [colAvoid, colFix, col, add_comm]
  exact Finset.card_filter_add_card_filter_not (s := G.colorings L) (fun f => f v = c)

/-- Colorings avoiding a color at a vertex are among all colorings. -/
theorem colAvoid_le_col (L : ListAssignment V) (v : V) (c : ℕ) : G.colAvoid L v c ≤ G.col L :=
  Nat.le.intro (colAvoid_add_colFix L v c)

/-- A color outside the list at `v` is avoided by every coloring. -/
theorem colAvoid_eq_col_of_notMem {L : ListAssignment V} {v : V} {c : ℕ} (hc : c ∉ L v) :
    G.colAvoid L v c = G.col L := by
  have h := colAvoid_add_colFix (G := G) L v c
  rwa [colFix_eq_zero_of_notMem hc, Nat.add_zero] at h

/-- Renaming the colors by an injective `e` is a bijection between the colorings from `L` whose
value at `v` satisfies `P ∘ e` and the colorings from the renamed lists whose value at `v`
satisfies `P`. -/
private lemma card_filter_colorings_image {L : ListAssignment V} {e : ℕ → ℕ}
    (he : Function.Injective e) (v : V) (P : ℕ → Prop) [DecidablePred P] :
    ((G.colorings fun u => (L u).image e).filter fun f => P (f v)).card
      = ((G.colorings L).filter fun f => P (e (f v))).card := by
  symm
  refine Finset.card_bij (fun f _ => e ∘ f) ?_ ?_ ?_
  · -- the renamed coloring is a coloring from the renamed lists
    intro f hf
    rw [Finset.mem_filter, mem_colorings] at hf ⊢
    refine ⟨⟨fun u => Finset.mem_image_of_mem e (hf.1.1 u), ?_⟩, hf.2⟩
    intro a b hab hcon
    exact hf.1.2 hab (he hcon)
  · -- injectivity
    intro f₁ _ f₂ _ heq
    funext u
    exact he (congrFun heq u)
  · -- surjectivity
    intro g hg
    rw [Finset.mem_filter, mem_colorings] at hg
    choose f hf₁ hf₂ using fun u => Finset.mem_image.mp (hg.1.1 u)
    refine ⟨f, ?_, funext hf₂⟩
    rw [Finset.mem_filter, mem_colorings]
    refine ⟨⟨hf₁, ?_⟩, ?_⟩
    · intro a b hab hcon
      exact hg.1.2 hab (by rw [← hf₂ a, ← hf₂ b, hcon])
    · rw [hf₂ v]
      exact hg.2

/-- Renaming the colors by an injective function transports `colFix`. -/
theorem colFix_image_of_injective {L : ListAssignment V} {e : ℕ → ℕ} (he : Function.Injective e)
    (v : V) (c : ℕ) : G.colFix (fun u => (L u).image e) v (e c) = G.colFix L v c := by
  rw [colFix, colFix, card_filter_colorings_image he v fun d => d = e c]
  congr 1
  exact Finset.filter_congr fun f _ => he.eq_iff

/-- Renaming the colors by an injective function transports `colAvoid`. -/
theorem colAvoid_image_of_injective {L : ListAssignment V} {e : ℕ → ℕ} (he : Function.Injective e)
    (v : V) (c : ℕ) : G.colAvoid (fun u => (L u).image e) v (e c) = G.colAvoid L v c := by
  rw [colAvoid, colAvoid, card_filter_colorings_image he v fun d => d ≠ e c]
  congr 1
  exact Finset.filter_congr fun f _ => not_congr he.eq_iff

end Avoid

/-! ### The bridged union -/

section Bridge

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The **bridged union** `bridge G H v₀ w₀`: the disjoint union `G ⊕g H` together with one extra
edge joining `Sum.inl v₀` to `Sum.inr w₀`. This is the paper's `G₁ ∪ G₂ + v₁v₂`. -/
def bridge (G : SimpleGraph V) (H : SimpleGraph W) (v₀ : V) (w₀ : W) : SimpleGraph (V ⊕ W) where
  Adj a b := (G ⊕g H).Adj a b ∨
    (a = .inl v₀ ∧ b = .inr w₀) ∨ (a = .inr w₀ ∧ b = .inl v₀)
  symm := ⟨fun a b h => by
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun a h => by
    rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact (G ⊕g H).irrefl h
    · simp at h
    · simp at h⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
variable (v₀ : V) (w₀ : W)

/-- Adjacency in a bridged union is decidable. -/
instance : DecidableRel (bridge G H v₀ w₀).Adj := fun a b =>
  inferInstanceAs (Decidable ((G ⊕g H).Adj a b ∨
    (a = .inl v₀ ∧ b = .inr w₀) ∨ (a = .inr w₀ ∧ b = .inl v₀)))

variable {G H v₀ w₀}

section AdjSimp
omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [DecidableRel G.Adj]
  [DecidableRel H.Adj]

/-- Inside the left-hand side, `bridge` is just `G`. -/
@[simp] lemma bridge_adj_inl_inl {a b : V} :
    (bridge G H v₀ w₀).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  simp [bridge]

/-- Inside the right-hand side, `bridge` is just `H`. -/
@[simp] lemma bridge_adj_inr_inr {a b : W} :
    (bridge G H v₀ w₀).Adj (.inr a) (.inr b) ↔ H.Adj a b := by
  simp [bridge]

/-- The only edge from the left-hand side to the right-hand side is the bridge. -/
@[simp] lemma bridge_adj_inl_inr {a : V} {b : W} :
    (bridge G H v₀ w₀).Adj (.inl a) (.inr b) ↔ (a = v₀ ∧ b = w₀) := by
  simp [bridge]

/-- The only edge from the right-hand side to the left-hand side is the bridge. -/
@[simp] lemma bridge_adj_inr_inl {a : W} {b : V} :
    (bridge G H v₀ w₀).Adj (.inr a) (.inl b) ↔ (a = w₀ ∧ b = v₀) := by
  simp [bridge]

/-- The bridging edge itself. -/
lemma bridge_adj_bridge : (bridge G H v₀ w₀).Adj (.inl v₀) (.inr w₀) := by simp

end AdjSimp

/-! ### Cutting along the bridge -/

/-- **Cutting along the bridge.** A coloring of `bridge G H v₀ w₀` giving the color `c` to `v₀` is
exactly a pair: a coloring of `G` giving `c` to `v₀`, and a coloring of `H` giving `w₀` any color
other than `c`. This holds unconditionally: if `c ∉ M (.inl v₀)` both sides vanish. -/
theorem colFix_bridge (M : ListAssignment (V ⊕ W)) (c : ℕ) :
    (bridge G H v₀ w₀).colFix M (.inl v₀) c
      = G.colFix (M ∘ Sum.inl) v₀ c * H.colAvoid (M ∘ Sum.inr) w₀ c := by
  rw [colFix, colFix, colAvoid, ← Finset.card_product]
  refine Finset.card_nbij' (fun f => (f ∘ Sum.inl, f ∘ Sum.inr)) (fun p => Sum.elim p.1 p.2)
    ?_ ?_ ?_ ?_
  · -- a coloring of the bridged graph splits into the required pair
    intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, mem_colorings] at hf
    obtain ⟨⟨hmem, hprop⟩, hv⟩ := hf
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, mem_colorings]
    refine ⟨⟨⟨fun v => hmem (.inl v), ?_⟩, hv⟩, ⟨fun w => hmem (.inr w), ?_⟩, ?_⟩
    · intro a b hab
      exact hprop (by simpa using hab)
    · intro a b hab
      exact hprop (by simpa using hab)
    · intro hcon
      exact hprop bridge_adj_bridge (hv.trans hcon.symm)
  · -- conversely, a pair assembles into a coloring of the bridged graph
    rintro ⟨g, h⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, mem_colorings] at hp
    obtain ⟨⟨⟨hg, hgp⟩, hgv⟩, ⟨hh, hhp⟩, hhw⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, mem_colorings]
    refine ⟨⟨?_, ?_⟩, hgv⟩
    · rintro (v | w)
      · exact hg v
      · exact hh w
    · rintro (a | a) (b | b) hab
      · exact hgp (by simpa using hab)
      · obtain ⟨rfl, rfl⟩ := bridge_adj_inl_inr.mp hab
        intro hcon
        exact hhw (by rw [← hgv]; exact hcon.symm)
      · obtain ⟨rfl, rfl⟩ := bridge_adj_inr_inl.mp hab
        intro hcon
        exact hhw (by rw [← hgv]; exact hcon)
      · exact hhp (by simpa using hab)
  · intro f _
    funext x
    cases x <;> rfl
  · rintro ⟨g, h⟩ _
    rfl

/-- **The bridged count.** Summing `colFix_bridge` over the colors available at `v₀`. -/
theorem col_bridge (M : ListAssignment (V ⊕ W)) :
    (bridge G H v₀ w₀).col M
      = ∑ c ∈ M (.inl v₀), G.colFix (M ∘ Sum.inl) v₀ c * H.colAvoid (M ∘ Sum.inr) w₀ c := by
  rw [sum_colFix M (.inl v₀)]
  exact Finset.sum_congr rfl fun c _ => colFix_bridge M c

/-! ### The swap step -/

/-- `swapRight M c₁ c₂` agrees with `M` on the left-hand side and applies the transposition
`Equiv.swap c₁ c₂` to every list on the right-hand side. -/
def swapRight (M : ListAssignment (V ⊕ W)) (c₁ c₂ : ℕ) : ListAssignment (V ⊕ W) :=
  Sum.elim (fun v => M (.inl v)) (fun w => (M (.inr w)).image (Equiv.swap c₁ c₂))

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- The lists on the left-hand side are untouched by `swapRight`. -/
@[simp] lemma swapRight_inl (M : ListAssignment (V ⊕ W)) (c₁ c₂ : ℕ) (v : V) :
    swapRight M c₁ c₂ (.inl v) = M (.inl v) := rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- The lists on the right-hand side are transposed by `swapRight`. -/
@[simp] lemma swapRight_inr (M : ListAssignment (V ⊕ W)) (c₁ c₂ : ℕ) (w : W) :
    swapRight M c₁ c₂ (.inr w) = (M (.inr w)).image (Equiv.swap c₁ c₂) := rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- **Part (a) of the swap step.** A transposition is injective, so `swapRight` preserves all the
list sizes. -/
theorem card_swapRight (M : ListAssignment (V ⊕ W)) (c₁ c₂ : ℕ) (x : V ⊕ W) :
    (swapRight M c₁ c₂ x).card = (M x).card := by
  cases x with
  | inl v => rfl
  | inr w => exact Finset.card_image_of_injective _ (Equiv.injective _)

omit [Fintype V] [DecidableEq V] in
/-- Avoiding `c` after the swap is avoiding `Equiv.swap c₁ c₂ c` before it. -/
theorem colAvoid_swapRight (M : ListAssignment (V ⊕ W)) (c₁ c₂ c : ℕ) :
    H.colAvoid (swapRight M c₁ c₂ ∘ Sum.inr) w₀ c
      = H.colAvoid (M ∘ Sum.inr) w₀ (Equiv.swap c₁ c₂ c) := by
  have h := colAvoid_image_of_injective (G := H) (L := M ∘ Sum.inr)
    (Equiv.injective (Equiv.swap c₁ c₂)) w₀ (Equiv.swap c₁ c₂ c)
  rwa [Equiv.swap_apply_self] at h

/-- **Part (b) of the swap step: the paper's equation (1)**, in subtraction-free form.

Swapping two colors `c₁ ∈ L(v₁) \ L(v₂)` and `c₂ ∈ L(v₂) \ L(v₁)` on the right-hand lists drops the
number of colorings by exactly `col(G, L, v₁, c₁) · col(H, L, v₂, c₂)`.

Note that the paper's hypothesis `c₂ ∈ L(v₂)` is not needed: if `c₂ ∉ L(v₂)` the correction term
vanishes and the identity just says that the swap changes nothing. -/
theorem col_swapRight_add (M : ListAssignment (V ⊕ W)) {c₁ c₂ : ℕ}
    (h₁ : c₁ ∈ M (.inl v₀)) (h₁' : c₁ ∉ M (.inr w₀)) (h₂' : c₂ ∉ M (.inl v₀)) :
    (bridge G H v₀ w₀).col (swapRight M c₁ c₂)
        + G.colFix (M ∘ Sum.inl) v₀ c₁ * H.colFix (M ∘ Sum.inr) w₀ c₂
      = (bridge G H v₀ w₀).col M := by
  -- rewrite the swapped count as a sum over the (unchanged) list at `v₀`
  have e1 : (bridge G H v₀ w₀).col (swapRight M c₁ c₂)
      = ∑ c ∈ M (.inl v₀), G.colFix (M ∘ Sum.inl) v₀ c
          * H.colAvoid (M ∘ Sum.inr) w₀ (Equiv.swap c₁ c₂ c) := by
    rw [col_bridge]
    exact Finset.sum_congr rfl fun c _ => by rw [colAvoid_swapRight]; rfl
  -- split off the `c₁` term on both sides
  have e2 : ∑ c ∈ M (.inl v₀), G.colFix (M ∘ Sum.inl) v₀ c
        * H.colAvoid (M ∘ Sum.inr) w₀ (Equiv.swap c₁ c₂ c)
      = (∑ c ∈ (M (.inl v₀)).erase c₁, G.colFix (M ∘ Sum.inl) v₀ c
          * H.colAvoid (M ∘ Sum.inr) w₀ c)
        + G.colFix (M ∘ Sum.inl) v₀ c₁ * H.colAvoid (M ∘ Sum.inr) w₀ c₂ := by
    rw [← Finset.sum_erase_add _ _ h₁]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hne1 : c ≠ c₁ := (Finset.mem_erase.mp hc).1
      have hne2 : c ≠ c₂ := fun h => h₂' (h ▸ Finset.mem_of_mem_erase hc)
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    · rw [Equiv.swap_apply_left]
  have e3 : (bridge G H v₀ w₀).col M
      = (∑ c ∈ (M (.inl v₀)).erase c₁, G.colFix (M ∘ Sum.inl) v₀ c
          * H.colAvoid (M ∘ Sum.inr) w₀ c)
        + G.colFix (M ∘ Sum.inl) v₀ c₁ * H.colAvoid (M ∘ Sum.inr) w₀ c₁ := by
    rw [col_bridge, ← Finset.sum_erase_add _ _ h₁]
  -- the `c₁` term of the original sum is `col(G,L,v₁,c₁) * col(H, L∘inr)`
  have hB1 : H.colAvoid (M ∘ Sum.inr) w₀ c₁ = H.col (M ∘ Sum.inr) :=
    colAvoid_eq_col_of_notMem h₁'
  have hB2 : H.colAvoid (M ∘ Sum.inr) w₀ c₂ + H.colFix (M ∘ Sum.inr) w₀ c₂
      = H.col (M ∘ Sum.inr) := colAvoid_add_colFix _ _ _
  rw [e1, e2, e3, add_assoc, ← Nat.mul_add, hB2, hB1]

/-- **Part (c) of the swap step.** The swap never increases the number of colorings. -/
theorem col_swapRight_le (M : ListAssignment (V ⊕ W)) {c₁ c₂ : ℕ}
    (h₁ : c₁ ∈ M (.inl v₀)) (h₁' : c₁ ∉ M (.inr w₀)) (h₂' : c₂ ∉ M (.inl v₀)) :
    (bridge G H v₀ w₀).col (swapRight M c₁ c₂) ≤ (bridge G H v₀ w₀).col M :=
  Nat.le.intro (col_swapRight_add M h₁ h₁' h₂')

/-- The paper's "moreover" clause: the swap *strictly* decreases the number of colorings as soon as
both prescribed counts are nonzero. -/
theorem col_swapRight_lt (M : ListAssignment (V ⊕ W)) {c₁ c₂ : ℕ}
    (h₁ : c₁ ∈ M (.inl v₀)) (h₁' : c₁ ∉ M (.inr w₀)) (h₂' : c₂ ∉ M (.inl v₀))
    (hG : G.colFix (M ∘ Sum.inl) v₀ c₁ ≠ 0) (hH : H.colFix (M ∘ Sum.inr) w₀ c₂ ≠ 0) :
    (bridge G H v₀ w₀).col (swapRight M c₁ c₂) < (bridge G H v₀ w₀).col M :=
  calc (bridge G H v₀ w₀).col (swapRight M c₁ c₂)
      < (bridge G H v₀ w₀).col (swapRight M c₁ c₂)
        + G.colFix (M ∘ Sum.inl) v₀ c₁ * H.colFix (M ∘ Sum.inr) w₀ c₂ :=
        Nat.lt_add_of_pos_right
          (Nat.mul_pos (Nat.pos_of_ne_zero hG) (Nat.pos_of_ne_zero hH))
    _ = (bridge G H v₀ w₀).col M := col_swapRight_add M h₁ h₁' h₂'

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- **Part (d) of the swap step.** The list at `w₀` after the swap: `c₂` is replaced by `c₁`. -/
theorem swapRight_inr_eq (M : ListAssignment (V ⊕ W)) {c₁ c₂ : ℕ}
    (h₁' : c₁ ∉ M (.inr w₀)) (h₂ : c₂ ∈ M (.inr w₀)) :
    swapRight M c₁ c₂ (.inr w₀) = insert c₁ ((M (.inr w₀)).erase c₂) := by
  ext x
  simp only [swapRight_inr, Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases hac : a = c₂
    · subst hac
      exact Or.inl (Equiv.swap_apply_right c₁ a)
    · have hac1 : a ≠ c₁ := fun h => h₁' (h ▸ ha)
      rw [Equiv.swap_apply_of_ne_of_ne hac1 hac]
      exact Or.inr ⟨hac, ha⟩
  · rintro (rfl | ⟨hx2, hxT⟩)
    · exact ⟨c₂, h₂, Equiv.swap_apply_right x c₂⟩
    · have hx1 : x ≠ c₁ := fun h => h₁' (h ▸ hxT)
      exact ⟨x, hxT, Equiv.swap_apply_of_ne_of_ne hx1 hx2⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- **The termination measure decreases.** The swap strictly shrinks the set of colors available at
`v₀` but not at `w₀`: it removes `c₁` and adds nothing. -/
theorem card_sdiff_swapRight_lt (M : ListAssignment (V ⊕ W)) {c₁ c₂ : ℕ}
    (h₁ : c₁ ∈ M (.inl v₀)) (h₁' : c₁ ∉ M (.inr w₀))
    (h₂ : c₂ ∈ M (.inr w₀)) (h₂' : c₂ ∉ M (.inl v₀)) :
    (M (.inl v₀) \ swapRight M c₁ c₂ (.inr w₀)).card < (M (.inl v₀) \ M (.inr w₀)).card := by
  have hsub : M (.inl v₀) \ swapRight M c₁ c₂ (.inr w₀)
      ⊆ (M (.inl v₀) \ M (.inr w₀)).erase c₁ := by
    intro x hx
    rw [Finset.mem_sdiff, swapRight_inr_eq M h₁' h₂, Finset.mem_insert, Finset.mem_erase] at hx
    obtain ⟨hxA, hxn⟩ := hx
    have hx1 : x ≠ c₁ := fun h => hxn (Or.inl h)
    have hx2 : x ≠ c₂ := fun h => h₂' (h ▸ hxA)
    have hxT : x ∉ M (.inr w₀) := fun h => hxn (Or.inr ⟨hx2, h⟩)
    rw [Finset.mem_erase, Finset.mem_sdiff]
    exact ⟨hx1, hxA, hxT⟩
  calc (M (.inl v₀) \ swapRight M c₁ c₂ (.inr w₀)).card
      ≤ ((M (.inl v₀) \ M (.inr w₀)).erase c₁).card := Finset.card_le_card hsub
    _ < (M (.inl v₀) \ M (.inr w₀)).card :=
        Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨h₁, h₁'⟩)

/-! ### Lemma 2 -/

/-- **Lemma 2 of Kirov–Naimi.** For any list assignment `M` of the bridged union
`bridge G H v₀ w₀` there is a list assignment `M'` with the same list sizes, whose lists at the two
endpoints of the bridge are nested, and with `col(bridge, M') ≤ col(bridge, M)`.

The proof iterates the swap step `swapRight`, which preserves list sizes, does not increase `col`,
and strictly decreases `(M (.inl v₀) \ M (.inr w₀)).card`. -/
theorem exists_nested_of_bridge (M : ListAssignment (V ⊕ W)) :
    ∃ M' : ListAssignment (V ⊕ W), (∀ x, (M' x).card = (M x).card) ∧
      (M' (.inl v₀) ⊆ M' (.inr w₀) ∨ M' (.inr w₀) ⊆ M' (.inl v₀)) ∧
      (bridge G H v₀ w₀).col M' ≤ (bridge G H v₀ w₀).col M := by
  suffices h : ∀ n (N : ListAssignment (V ⊕ W)), (N (.inl v₀) \ N (.inr w₀)).card ≤ n →
      ∃ N' : ListAssignment (V ⊕ W), (∀ x, (N' x).card = (N x).card) ∧
        (N' (.inl v₀) ⊆ N' (.inr w₀) ∨ N' (.inr w₀) ⊆ N' (.inl v₀)) ∧
        (bridge G H v₀ w₀).col N' ≤ (bridge G H v₀ w₀).col N by
    exact h _ M le_rfl
  intro n
  induction n with
  | zero =>
    intro N hN
    refine ⟨N, fun _ => rfl, Or.inl ?_, le_rfl⟩
    rw [← Finset.sdiff_eq_empty_iff_subset]
    exact Finset.card_eq_zero.mp (Nat.le_zero.mp hN)
  | succ n ih =>
    intro N hN
    by_cases hsub : N (.inl v₀) ⊆ N (.inr w₀)
    · exact ⟨N, fun _ => rfl, Or.inl hsub, le_rfl⟩
    by_cases hsub' : N (.inr w₀) ⊆ N (.inl v₀)
    · exact ⟨N, fun _ => rfl, Or.inr hsub', le_rfl⟩
    obtain ⟨c₁, hc₁, hc₁'⟩ := Finset.not_subset.mp hsub
    obtain ⟨c₂, hc₂, hc₂'⟩ := Finset.not_subset.mp hsub'
    have hlt := card_sdiff_swapRight_lt (v₀ := v₀) (w₀ := w₀) N hc₁ hc₁' hc₂ hc₂'
    obtain ⟨N', hcard, hnest, hle⟩ := ih (swapRight N c₁ c₂) (by
      have : swapRight N c₁ c₂ (.inl v₀) = N (.inl v₀) := rfl
      rw [this]
      omega)
    exact ⟨N', fun x => (hcard x).trans (card_swapRight N c₁ c₂ x), hnest,
      hle.trans (col_swapRight_le N hc₁ hc₁' hc₂')⟩

end Bridge

end SimpleGraph
