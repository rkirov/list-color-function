/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Rooted

/-!
# Weighted coloring counts

The block induction (handoff §4) attaches **weights** to vertices: when a subtree hangs off a
cut vertex `v`, its rooted profile becomes a per-colour weight multiplying every coloring of
the rest. `wcol` is the weighted partition function `Z(w) = ∑_f ∏_v w v (f v)` over proper
`L`-colorings; weights are natural numbers, because the weights that actually occur are rooted
coloring counts.

* `wcol_const_one` — trivial weights recover `col`;
* `wcol_eq_sum_rootedWcol` — partition over the root's colour;
* `rootedWcol_mul_of_cut` — the weighted cut-vertex product (the message-passing step).
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **weighted count**: proper `L`-colorings, each weighted by the product over vertices of
the vertex's weight at its colour. -/
def wcol (L : ListAssignment V) (w : V → ℕ → ℕ) : ℕ :=
  ∑ f ∈ G.colorings L, ∏ v, w v (f v)

/-- The **weighted rooted count**. -/
def rootedWcol (L : ListAssignment V) (w : V → ℕ → ℕ) (r : V) (c : ℕ) : ℕ :=
  ∑ f ∈ (G.colorings L).filter (fun f => f r = c), ∏ v, w v (f v)

@[simp] theorem wcol_const_one (L : ListAssignment V) :
    wcol G L (fun _ _ => 1) = G.col L := by
  rw [wcol, SimpleGraph.col]
  simp

/-- The weighted count partitions over the root's list. -/
theorem wcol_eq_sum_rootedWcol (L : ListAssignment V) (w : V → ℕ → ℕ) (r : V) :
    wcol G L w = ∑ c ∈ L r, rootedWcol G L w r c := by
  rw [wcol, ← Finset.sum_fiberwise_of_maps_to
    (fun f hf => G.mem_list_of_mem_colorings hf r) (fun f => ∏ v, w v (f v))]
  rfl


section WeightedCut

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Splitting a product over all vertices along a cover `A ∪ B` meeting exactly at `r`, with
the `r`-factor charged to the `A` side. -/
theorem prod_split_of_cut {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {r : V} (hrA : r ∈ A) (hrB : r ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = r) (F : V → ℕ) :
    ∏ v, F v = (∏ v : A, F v.val) * (∏ v : B, if v.val = r then 1 else F v.val) := by
  have hsub : ∀ (s : Set V) [DecidablePred (· ∈ s)] (H : V → ℕ),
      (∏ v : s, H v.val) = ∏ v ∈ s.toFinset, H v := by
    intro s _ H
    rw [← Finset.prod_subtype s.toFinset (fun v => Set.mem_toFinset) H]
  rw [hsub A F, hsub B (fun x => if x = r then 1 else F x)]
  have hB : (∏ v ∈ B.toFinset, if v = r then 1 else F v)
      = ∏ v ∈ B.toFinset.erase r, F v := by
    rw [← Finset.mul_prod_erase B.toFinset _ (Set.mem_toFinset.mpr hrB), if_pos rfl, one_mul]
    exact Finset.prod_congr rfl fun v hv => if_neg (Finset.ne_of_mem_erase hv)
  rw [hB, ← Finset.prod_union (by
    rw [Finset.disjoint_right]
    intro v hv hvA
    have hvB : v ∈ B.toFinset.erase r → v ∈ B := fun h => Set.mem_toFinset.mp (Finset.mem_of_mem_erase h)
    exact Finset.ne_of_mem_erase hv (hmeet v (Set.mem_toFinset.mp hvA) (hvB hv)))]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext v
  simp only [Finset.mem_union, Set.mem_toFinset, Finset.mem_erase, Finset.mem_univ, true_iff]
  rcases hcover v with h | h
  · exact Or.inl h
  · by_cases hvr : v = r
    · exact Or.inl (hvr ▸ hrA)
    · exact Or.inr ⟨hvr, h⟩

/-- **The weighted cut-vertex product**: rooted weighted counts multiply across a cut, with the
root's weight charged to the `A` side. This is the message-passing step of the block
induction. -/
theorem rootedWcol_mul_of_cut {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {r : V} (hrA : r ∈ A) (hrB : r ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = r)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (L : ListAssignment V) (w : V → ℕ → ℕ) (c : ℕ) :
    rootedWcol G L w r c =
      rootedWcol (G.induce A) (fun v => L v) (fun v d => w v.val d) ⟨r, hrA⟩ c *
        rootedWcol (G.induce B) (fun v => L v)
          (fun v d => if v.val = r then 1 else w v.val d) ⟨r, hrB⟩ c := by
  rw [rootedWcol, rootedWcol, rootedWcol, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_bij' (fun f _ => (fun v => f v.val, fun v => f v.val))
    (fun p _ => fun v => if hv : v ∈ A then p.1 ⟨v, hv⟩ else p.2 ⟨v, (hcover v).resolve_left hv⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfc, hfr⟩ := hf
    rw [SimpleGraph.mem_colorings_iff] at hfc
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff]
    exact ⟨⟨⟨fun v => hfc.1 v.val, fun v u hadj => hfc.2 v.val u.val hadj⟩, hfr⟩,
      ⟨⟨fun v => hfc.1 v.val, fun v u hadj => hfc.2 v.val u.val hadj⟩, hfr⟩⟩
  · -- backward membership
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff] at hp
    obtain ⟨⟨⟨h1mem, h1prop⟩, h1r⟩, ⟨⟨h2mem, h2prop⟩, h2r⟩⟩ := hp
    have hglueB : ∀ (v : V) (hv : v ∈ B),
        (if hv' : v ∈ A then p.1 ⟨v, hv'⟩ else p.2 ⟨v, (hcover v).resolve_left hv'⟩)
          = p.2 ⟨v, hv⟩ := by
      intro v hv
      by_cases hv' : v ∈ A
      · rw [dif_pos hv']
        have hveq : v = r := hmeet v hv' hv
        subst hveq
        rw [h1r, ← h2r]
      · rw [dif_neg hv']
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v
      by_cases hv : v ∈ A
      · rw [dif_pos hv]; exact h1mem ⟨v, hv⟩
      · rw [dif_neg hv]; exact h2mem _
    · intro v u hadj
      rcases hedge v u hadj with ⟨hvA, huA⟩ | ⟨hvB, huB⟩
      · rw [dif_pos hvA, dif_pos huA]
        exact h1prop ⟨v, hvA⟩ ⟨u, huA⟩ hadj
      · rw [hglueB v hvB, hglueB u huB]
        exact h2prop ⟨v, hvB⟩ ⟨u, huB⟩ hadj
    · show (if hv : r ∈ A then p.1 ⟨r, hv⟩ else p.2 ⟨r, (hcover r).resolve_left hv⟩) = c
      rw [dif_pos hrA]; exact h1r
  · -- left inverse
    intro f hf
    funext v
    by_cases hv : v ∈ A
    · rw [dif_pos hv]
    · rw [dif_neg hv]
  · -- right inverse
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, h1r⟩, ⟨_, h2r⟩⟩ := hp
    have hcoh : ∀ (v : V) (hvA : v ∈ A) (hv : v ∈ B), p.1 ⟨v, hvA⟩ = p.2 ⟨v, hv⟩ := by
      intro v hvA hv
      have hveq : v = r := hmeet v hvA hv
      subst hveq
      rw [h1r, ← h2r]
    refine Prod.ext ?_ ?_
    · funext v
      show (if hv : v.val ∈ A then _ else _) = p.1 v
      rw [dif_pos v.property]
    · funext v
      show (if hv : v.val ∈ A then _ else _) = p.2 v
      by_cases hv : v.val ∈ A
      · rw [dif_pos hv]
        exact hcoh v.val hv v.property
      · rw [dif_neg hv]
  · -- the summand matches: the weight product splits
    intro f hf
    exact prod_split_of_cut hrA hrB hcover hmeet (fun v => w v (f v))

end WeightedCut

end ListColoring
