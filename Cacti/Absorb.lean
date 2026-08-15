/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Weighted

/-!
# The absorption lemma

The single decomposition step of the block induction: when a piece `B` of the graph hangs off
the rest `A` at a cut vertex `u`, and the root lies in `A`, the whole piece is **absorbed**
into the weight at `u` — the new weight of colour `d` at `u` is the old one times the
`B`-side rooted weighted count at colour `d` (with `u`'s own weight charged to the `A` side).

Pendant vertices, bridges, and leaf cycles are all instances.
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Absorption**: with `V` covered by `A ∪ B` meeting exactly at `u`, all edges inside a
side, and the root `r` in `A`, the rooted weighted count of `G` is that of `G.induce A` with
the weight at `u` multiplied by the `B`-side profile. -/
theorem rootedWcol_absorb {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {u : V} (huA : u ∈ A) (huB : u ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = u)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {r : V} (hrA : r ∈ A)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (c : ℕ) :
    rootedWcol G L w r c =
      rootedWcol (G.induce A) (fun v => L v)
        (fun v d => if v.val = u then
            w u d * rootedWcol (G.induce B) (fun x => L x)
              (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ d
          else w v.val d) ⟨r, hrA⟩ c := by
  set wB : B → ℕ → ℕ := fun x e => if x.val = u then 1 else w x.val e with hwB
  set msg : ℕ → ℕ := fun d =>
    rootedWcol (G.induce B) (fun x => L x) wB ⟨u, huB⟩ d with hmsg
  -- Step 1: the global sum equals the sum over matched pairs.
  have step1 : rootedWcol G L w r c =
      ∑ g ∈ ((G.induce A).colorings (fun v => L v)).filter (fun g => g ⟨r, hrA⟩ = c),
        (∏ v, w v.val (g v)) * msg (g ⟨u, huA⟩) := by
    rw [rootedWcol]
    -- expand msg as an inner filtered sum and turn the double sum into a sum over pairs
    simp only [hmsg, rootedWcol, Finset.mul_sum]
    rw [Finset.sum_sigma']
    -- bijection between colorings of `G` fixing `r ↦ c` and matched pairs
    refine Finset.sum_nbij' (fun f => ⟨fun v => f v.val, fun v => f v.val⟩)
      (fun p => fun v => if hv : v ∈ A then p.1 ⟨v, hv⟩ else p.2 ⟨v, (hcover v).resolve_left hv⟩)
      ?_ ?_ ?_ ?_ ?_
    · -- forward membership
      intro f hf
      rw [Finset.mem_filter] at hf
      obtain ⟨hfc, hfr⟩ := hf
      rw [SimpleGraph.mem_colorings_iff] at hfc
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter,
        SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff]
      exact ⟨⟨⟨fun v => hfc.1 v.val, fun v x hadj => hfc.2 v.val x.val hadj⟩, hfr⟩,
        ⟨⟨fun v => hfc.1 v.val, fun v x hadj => hfc.2 v.val x.val hadj⟩, rfl⟩⟩
    · -- backward membership
      intro p hp
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter,
        SimpleGraph.mem_colorings_iff, SimpleGraph.mem_colorings_iff] at hp
      obtain ⟨⟨⟨h1mem, h1prop⟩, h1r⟩, ⟨⟨h2mem, h2prop⟩, h2u⟩⟩ := hp
      have hglueB : ∀ (v : V) (hv : v ∈ B),
          (if hv' : v ∈ A then p.1 ⟨v, hv'⟩ else p.2 ⟨v, (hcover v).resolve_left hv'⟩)
            = p.2 ⟨v, hv⟩ := by
        intro v hv
        by_cases hv' : v ∈ A
        · rw [dif_pos hv']
          have hveq : v = u := hmeet v hv' hv
          subst hveq
          rw [h2u]
        · rw [dif_neg hv']
      rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro v
        by_cases hv : v ∈ A
        · rw [dif_pos hv]; exact h1mem ⟨v, hv⟩
        · rw [dif_neg hv]; exact h2mem _
      · intro v x hadj
        rcases hedge v x hadj with ⟨hvA, hxA⟩ | ⟨hvB, hxB⟩
        · rw [dif_pos hvA, dif_pos hxA]
          exact h1prop ⟨v, hvA⟩ ⟨x, hxA⟩ hadj
        · rw [hglueB v hvB, hglueB x hxB]
          exact h2prop ⟨v, hvB⟩ ⟨x, hxB⟩ hadj
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
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨_, h1r⟩, ⟨_, h2u⟩⟩ := hp
      have hcoh : ∀ (v : V) (hvA : v ∈ A) (hv : v ∈ B), p.1 ⟨v, hvA⟩ = p.2 ⟨v, hv⟩ := by
        intro v hvA hv
        have hveq : v = u := hmeet v hvA hv
        subst hveq
        rw [h2u]
      have h1 : (fun (v : A) => (if hv : (v : V) ∈ A then p.1 ⟨v, hv⟩
          else p.2 ⟨v, (hcover v).resolve_left hv⟩)) = p.1 := by
        funext v
        show (if hv : v.val ∈ A then _ else _) = p.1 v
        rw [dif_pos v.property]
      have h2 : (fun (v : B) => (if hv : (v : V) ∈ A then p.1 ⟨v, hv⟩
          else p.2 ⟨v, (hcover v).resolve_left hv⟩)) = p.2 := by
        funext v
        show (if hv : v.val ∈ A then _ else _) = p.2 v
        by_cases hv : v.val ∈ A
        · rw [dif_pos hv]
          exact hcoh v.val hv v.property
        · rw [dif_neg hv]
      exact Sigma.ext h1 (heq_of_eq h2)
    · -- the summand matches
      intro f hf
      have hsplit := prod_split_of_cut huA huB hcover hmeet (fun v => w v (f v))
      rw [hsplit]
  -- Step 2: fold the message into the `A`-side weight.
  rw [step1, rootedWcol]
  refine Finset.sum_congr rfl fun g hg => ?_
  show (∏ v, w v.val (g v)) * msg (g ⟨u, huA⟩)
      = ∏ v : A, (if v.val = u then w u (g v) * msg (g v) else w v.val (g v))
  have hu' : (⟨u, huA⟩ : A) ∈ (Finset.univ : Finset A) := Finset.mem_univ _
  have herase : (∏ x ∈ Finset.univ.erase (⟨u, huA⟩ : A),
        (if x.val = u then w u (g x) * msg (g x) else w x.val (g x)))
      = ∏ x ∈ Finset.univ.erase (⟨u, huA⟩ : A), w x.val (g x) :=
    Finset.prod_congr rfl fun v hv =>
      if_neg (fun h => Finset.ne_of_mem_erase hv (Subtype.ext h))
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v => if v.val = u then w u (g v) * msg (g v) else w v.val (g v)) hu',
    ← Finset.mul_prod_erase Finset.univ (fun v => w v.val (g v)) hu', herase, if_pos rfl]
  ring


section Pendant

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Weights agreeing on list members give equal rooted weighted counts. -/
theorem rootedWcol_weight_congr {L : ListAssignment V} {w w' : V → ℕ → ℕ}
    (h : ∀ v d, d ∈ L v → w v d = w' v d) (r : V) (c : ℕ) :
    rootedWcol G L w r c = rootedWcol G L w' r c := by
  refine Finset.sum_congr rfl fun f hf => ?_
  refine Finset.prod_congr rfl fun v _ => ?_
  exact h v (f v) (G.mem_list_of_mem_colorings (Finset.mem_filter.mp hf).1 v)

/-- The rooted weighted count of an edge `u—x`, rooted at `u` with colour `d ∈ L u` and the
`u`-weight trivial: the sum of the `x`-weights over the colours of `L x` other than `d`. -/
theorem rootedWcol_edge {u x : V} (hux : G.Adj u x)
    (hBedge : ∀ a b, G.Adj a b → a ∈ ({u, x} : Set V) → b ∈ ({u, x} : Set V) →
      (a = u ∧ b = x) ∨ (a = x ∧ b = u))
    (L : ListAssignment V) (w : V → ℕ → ℕ) {d : ℕ} (hd : d ∈ L u)
    {instF : Fintype (({u, x} : Set V) : Type _)}
    {instD : DecidableRel (G.induce ({u, x} : Set V)).Adj} :
    rootedWcol (G.induce ({u, x} : Set V)) (fun v => L v)
        (fun v e => if v.val = u then 1 else w v.val e)
        ⟨u, Or.inl rfl⟩ d
      = ∑ e ∈ (L x).filter (· ≠ d), w x e := by
  have hne : u ≠ x := hux.ne
  have huniv : (Finset.univ : Finset ({u, x} : Set V)) =
      {⟨u, Or.inl rfl⟩, ⟨x, Or.inr rfl⟩} := by
    ext v
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases v.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rw [rootedWcol]
  refine Finset.sum_nbij' (fun f => f ⟨x, Or.inr rfl⟩)
    (fun e => fun v => if v.val = u then d else e) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfc, hfu⟩ := hf
    rw [SimpleGraph.mem_colorings_iff] at hfc
    rw [Finset.mem_filter]
    refine ⟨hfc.1 _, ?_⟩
    intro hcontra
    exact hfc.2 ⟨u, Or.inl rfl⟩ ⟨x, Or.inr rfl⟩ hux (by rw [hfu, hcontra])
  · -- backward membership
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hemem, hene⟩ := he
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v
      rcases v.property with h | h
      · have : v.val = u := h
        rw [if_pos this]
        show d ∈ L v.val
        rw [this]
        exact hd
      · have hvx : v.val = x := h
        by_cases hvu : v.val = u
        · rw [if_pos hvu]
          show d ∈ L v.val
          rw [hvu]
          exact hd
        · rw [if_neg hvu]
          show e ∈ L v.val
          rw [hvx]
          exact hemem
    · intro a b hadj
      rcases hBedge a.val b.val hadj a.property b.property with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [if_pos ha, if_neg (fun h => hne.symm (hb.symm.trans h))]
        exact fun h => hene h.symm
      · rw [if_neg (fun h => hne.symm (ha.symm.trans h)), if_pos hb]
        exact hene
    · show (if (u : V) = u then d else e) = d
      rw [if_pos rfl]
  · -- left inverse
    intro f hf
    rw [Finset.mem_filter] at hf
    funext v
    by_cases hvu : v.val = u
    · show (if v.val = u then d else _) = f v
      rw [if_pos hvu, ← hf.2]
      congr 1
      exact Subtype.ext hvu.symm
    · show (if v.val = u then d else f ⟨x, Or.inr rfl⟩) = f v
      rw [if_neg hvu]
      congr 1
      exact Subtype.ext (by
        rcases v.property with h | h
        · exact absurd h hvu
        · exact h.symm)
  · -- right inverse
    intro e he
    show (if (x : V) = u then d else e) = e
    rw [if_neg hne.symm]
  · -- summand
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [huniv, Finset.prod_insert (by
      simp only [Finset.mem_singleton]
      intro h
      exact hne (congrArg Subtype.val h)), Finset.prod_singleton]
    show (if (u : V) = u then 1 else w u _) * (if (x : V) = u then 1 else w x _) = w x _
    rw [if_pos rfl, if_neg hne.symm, one_mul]


set_option maxHeartbeats 1600000 in
/-- **Pendant absorption**: a degree-one vertex `x` with unique neighbour `u` is absorbed into
the weight at `u` — the new weight of colour `d` is the old one times the total `x`-weight of
the colours of `L x` other than `d`. -/
theorem rootedWcol_pendant {x u : V} (hxu : G.Adj x u) (huniq : ∀ y, G.Adj x y → y = u)
    {r : V} (hrx : r ≠ x) (L : ListAssignment V) (w : V → ℕ → ℕ) (c : ℕ) :
    rootedWcol G L w r c =
      rootedWcol (G.induce {y | y ≠ x}) (fun v => L v)
        (fun v d => if v.val = u then w u d * ∑ e ∈ (L x).filter (· ≠ d), w x e
          else w v.val d) ⟨r, hrx⟩ c := by
  letI : DecidablePred (· ∈ {y : V | y ≠ x}) := fun v => inferInstanceAs (Decidable (v ≠ x))
  letI : DecidablePred (· ∈ ({u, x} : Set V)) :=
    fun v => inferInstanceAs (Decidable (v = u ∨ v = x))
  have hux : u ≠ x := hxu.ne'
  have habs := rootedWcol_absorb (A := {y | y ≠ x}) (B := ({u, x} : Set V))
    (u := u) hux (Or.inl rfl)
    (fun v => by
      by_cases hvx : v = x
      · exact Or.inr (Or.inr hvx)
      · exact Or.inl hvx)
    (fun v hvA hvB => by
      rcases hvB with h | h
      · exact h
      · exact absurd h hvA)
    (fun a b hadj => by
      by_cases hax : a = x
      · subst hax
        exact Or.inr ⟨Or.inr rfl, Or.inl (huniq b hadj)⟩
      · by_cases hbx : b = x
        · subst hbx
          exact Or.inr ⟨Or.inl (huniq a hadj.symm), Or.inr rfl⟩
        · exact Or.inl ⟨hax, hbx⟩)
    hrx L w c
  rw [habs]
  refine rootedWcol_weight_congr (fun v d hd => ?_) _ _
  by_cases hvu : v.val = u
  · rw [if_pos hvu, if_pos hvu]
    congr 1
    have hdu : d ∈ L u := by rw [← hvu]; exact hd
    have hBedge : ∀ a b, G.Adj a b → a ∈ ({u, x} : Set V) → b ∈ ({u, x} : Set V) →
        (a = u ∧ b = x) ∨ (a = x ∧ b = u) := by
      intro a b hadj ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.symm ▸ hb.symm ▸ hadj) (G.irrefl)
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact absurd (ha.symm ▸ hb.symm ▸ hadj) (G.irrefl)
    exact rootedWcol_edge hxu.symm hBedge L w hdu
  · rw [if_neg hvu, if_neg hvu]


/-- The rooted weighted count of an edge `u—x` with **full weights**, the weight given
directly on the subtype: the root's weight times the complementary weighted sum at the other
end. -/
theorem rootedWcol_edge_full {u x : V} (hux : G.Adj u x)
    (hBedge : ∀ a b, G.Adj a b → a ∈ ({u, x} : Set V) → b ∈ ({u, x} : Set V) →
      (a = u ∧ b = x) ∨ (a = x ∧ b = u))
    (L : ListAssignment V) {d : ℕ} (hd : d ∈ L u)
    {instF : Fintype (({u, x} : Set V) : Type _)}
    {instD : DecidableRel (G.induce ({u, x} : Set V)).Adj}
    (w' : (({u, x} : Set V) : Type _) → ℕ → ℕ)
    (hmemu : u ∈ ({u, x} : Set V)) (hmemx : x ∈ ({u, x} : Set V)) :
    rootedWcol (G.induce ({u, x} : Set V)) (fun v => L v) w' ⟨u, hmemu⟩ d
      = w' ⟨u, hmemu⟩ d * ∑ e ∈ (L x).filter (· ≠ d), w' ⟨x, hmemx⟩ e := by
  have hne : u ≠ x := hux.ne
  have huniv : (Finset.univ : Finset (({u, x} : Set V) : Type _)) =
      {⟨u, hmemu⟩, ⟨x, hmemx⟩} := by
    ext v
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases v.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rw [rootedWcol, Finset.mul_sum]
  refine Finset.sum_nbij' (fun f => f ⟨x, hmemx⟩)
    (fun e => fun v => if v.val = u then d else e) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfc, hfu⟩ := hf
    rw [SimpleGraph.mem_colorings_iff] at hfc
    rw [Finset.mem_filter]
    refine ⟨hfc.1 _, ?_⟩
    intro hcontra
    exact hfc.2 ⟨u, hmemu⟩ ⟨x, hmemx⟩ hux (by rw [hfu, hcontra])
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hemem, hene⟩ := he
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v
      rcases v.property with h | h
      · have : v.val = u := h
        rw [if_pos this]
        show d ∈ L v.val
        rw [this]
        exact hd
      · have hvx : v.val = x := h
        by_cases hvu : v.val = u
        · rw [if_pos hvu]
          show d ∈ L v.val
          rw [hvu]
          exact hd
        · rw [if_neg hvu]
          show e ∈ L v.val
          rw [hvx]
          exact hemem
    · intro a b hadj
      rcases hBedge a.val b.val hadj a.property b.property with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [if_pos ha, if_neg (fun h => hne.symm (hb.symm.trans h))]
        exact fun h => hene h.symm
      · rw [if_neg (fun h => hne.symm (ha.symm.trans h)), if_pos hb]
        exact hene
    · show (if (u : V) = u then d else e) = d
      rw [if_pos rfl]
  · intro f hf
    rw [Finset.mem_filter] at hf
    funext v
    by_cases hvu : v.val = u
    · show (if v.val = u then d else _) = f v
      rw [if_pos hvu, ← hf.2]
      congr 1
      exact Subtype.ext hvu.symm
    · show (if v.val = u then d else f ⟨x, hmemx⟩) = f v
      rw [if_neg hvu]
      congr 1
      exact Subtype.ext (by
        rcases v.property with h | h
        · exact absurd h hvu
        · exact h.symm)
  · intro e he
    show (if (x : V) = u then d else e) = e
    rw [if_neg hne.symm]
  · intro f hf
    rw [Finset.mem_filter] at hf
    have hnesub : (⟨u, hmemu⟩ : (({u, x} : Set V) : Type _)) ∉
        ({⟨x, hmemx⟩} : Finset (({u, x} : Set V) : Type _)) := by
      simp only [Finset.mem_singleton]
      intro h
      exact hne (congrArg Subtype.val h)
    rw [huniv, Finset.prod_insert hnesub, Finset.prod_singleton, hf.2]

end Pendant

end ListColoring
