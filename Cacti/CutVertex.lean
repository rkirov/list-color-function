/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.LeafPeeling

/-!
# Cut vertices of a cactus

The structural input of the `k ≥ 4` induction (handoff §6.5) is that a cactus with no pendant
vertex is a single cycle or splits at a cut vertex. Here is the half that makes a cut vertex
appear: **in a cactus, a vertex of degree at least three is a cut vertex.**

The argument is the defining property of a cactus, used once. If deleting `u` left the graph
connected, then any two of its neighbours would be joined by a path avoiding `u`, and three
neighbours `x, y, z` would give two cycles through `u` — one closing through `y`, one through
`z` — sharing the edge `u—x`. A cactus forces them to have the same edge set, yet the second
cycle's only edges at `u` are `u—x` and `u—z`, and `u—y` is neither.

From there `exists_cut_split_of_three_le_degree` assembles the split the induction consumes: the
component of a neighbour in `G - u` together with `u` on one side, everything else on the other.
`exists_leaf_cut_split` is the easy companion — a pendant vertex splits off its own edge — which
together with the degree-three case turns the block induction into a three-way split (see
`exists_cut_split_or_cyclic_index_of_three_le`).
-/

namespace ListColoring

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three distinct neighbours of a vertex of degree at least three. -/
theorem exists_three_adj {u : V} (hu : 3 ≤ G.degree u) :
    ∃ x y z : V, G.Adj u x ∧ G.Adj u y ∧ G.Adj u z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  have h3 : 3 ≤ (G.neighborFinset u).card := hu
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset u).card by omega)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp
    (show 0 < ((G.neighborFinset u).erase x).card by
      rw [Finset.card_erase_of_mem hx]; omega)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp
    (show 0 < (((G.neighborFinset u).erase x).erase y).card by
      rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]; omega)
  exact ⟨x, y, z, (G.mem_neighborFinset u x).mp hx,
    (G.mem_neighborFinset u y).mp (Finset.mem_of_mem_erase hy),
    (G.mem_neighborFinset u z).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)),
    (Finset.ne_of_mem_erase hy).symm,
    (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)).symm,
    (Finset.ne_of_mem_erase hz).symm⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The cycle through `u` closed by a path between two of its neighbours that avoids `u`, with
its edge list read off. -/
theorem exists_isCycle_of_avoiding_path {u a b : V} (ha : G.Adj u a) (hb : G.Adj u b)
    (hab : a ≠ b) {p : G.Walk a b} (hp : p.IsPath) (hpu : u ∉ p.support) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.edges = s(u, a) :: (p.edges ++ [s(b, u)]) := by
  have hedge : s(u, a) ∉ (p.concat hb.symm).edges := by
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append]
    rintro (hin | hin)
    · exact hpu (p.fst_mem_support_of_mem_edges hin)
    · rw [List.mem_singleton, Sym2.eq_iff] at hin
      rcases hin with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1.symm hb.ne'
      · exact hab h2
  refine ⟨Walk.cons ha (p.concat hb.symm), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    exact ⟨hp.concat hpu hb.symm, hedge⟩
  · rw [Walk.edges_cons, Walk.edges_concat, List.concat_eq_append]

/-- **A vertex of degree at least three in a cactus is a cut vertex**: two of its neighbours are
unreachable from each other once it is deleted. -/
theorem exists_nonreachable_adj_of_three_le_degree (hG : IsCactus G) {u : V}
    (hu : 3 ≤ G.degree u) :
    ∃ (x y : V) (hx : x ≠ u) (hy : y ≠ u), G.Adj u x ∧ G.Adj u y ∧
      ¬ (G.induce {v : V | v ≠ u}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, z, hax, hay, haz, hxy, hxz, hyz⟩ := exists_three_adj hu
  -- with no such pair, any two neighbours of `u` are joined by a path avoiding `u`
  have hpath : ∀ a b : V, G.Adj u a → G.Adj u b →
      ∃ p : G.Walk a b, p.IsPath ∧ u ∉ p.support := by
    intro a b ha hb
    obtain ⟨W⟩ := hcon a b ha.ne' hb.ne' ha hb
    refine ⟨(W.map (induceVal G _)).bypass, Walk.bypass_isPath _, fun hmem => ?_⟩
    have hsub := Walk.support_bypass_subset_support (W.map (induceVal G _)) hmem
    rw [Walk.support_map, List.mem_map] at hsub
    obtain ⟨w, -, hw⟩ := hsub
    exact w.2 hw
  obtain ⟨p, hp, hpu⟩ := hpath x y hax hay
  obtain ⟨q, hq, hqu⟩ := hpath x z hax haz
  obtain ⟨c₁, hc₁, he₁⟩ := exists_isCycle_of_avoiding_path hax hay hxy hp hpu
  obtain ⟨c₂, hc₂, he₂⟩ := exists_isCycle_of_avoiding_path hax haz hxz hq hqu
  -- both cycles carry the edge `u—x`, so a cactus forces one edge set
  have hsets := hG.2 c₁ c₂ hc₁ hc₂ s(u, x)
    (by rw [he₁]; exact List.mem_cons_self ..) (by rw [he₂]; exact List.mem_cons_self ..)
  -- the first cycle's edge `u—y` is then one of the second's, and it is none of them
  have hy₁ : s(u, y) ∈ c₁.edges := by
    rw [he₁]
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    rw [List.mem_singleton, Sym2.eq_swap]
  have hy₂ : s(u, y) ∈ c₂.edges := by
    have hmem := List.mem_toFinset.mpr hy₁
    rw [hsets, List.mem_toFinset] at hmem
    exact hmem
  rw [he₂] at hy₂
  rcases List.mem_cons.mp hy₂ with h | h
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hxy h2.symm
    · exact absurd h1 hax.ne
  · rcases List.mem_append.mp h with h | h
    · exact hqu (q.fst_mem_support_of_mem_edges h)
    · rw [List.mem_singleton, Sym2.eq_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 haz.ne
      · exact hyz h2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A walk of an induced subgraph whose vertices all lie in another set is a walk there. -/
theorem exists_walk_induce_of_support {T T' : Set V} {a b : T} (W : (G.induce T).Walk a b) :
    ∀ (ha : a.val ∈ T') (hb : b.val ∈ T'), (∀ w ∈ W.support, w.val ∈ T') →
      Nonempty ((G.induce T').Walk ⟨a.val, ha⟩ ⟨b.val, hb⟩) := by
  induction W with
  | nil => intro _ _ _; exact ⟨Walk.nil⟩
  | @cons c d e hadj p ih =>
    intro ha hb hsupp
    have hd : d.val ∈ T' := hsupp d (by
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ p.start_mem_support)
    obtain ⟨p'⟩ := ih hd hb (fun w hw => hsupp w (by
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ hw))
    exact ⟨Walk.cons (show (G.induce T').Adj ⟨c.val, ha⟩ ⟨d.val, hd⟩ from hadj) p'⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- The cycle condition of a cactus passes to every induced subgraph. -/
theorem isCactus_edges_induce (hG : IsCactus G) (T : Set V) :
    ∀ ⦃a b : T⦄ (p : (G.induce T).Walk a a) (q : (G.induce T).Walk b b),
      p.IsCycle → q.IsCycle → ∀ e ∈ p.edges, e ∈ q.edges →
        p.edges.toFinset = q.edges.toFinset := by
  intro a b p q hp hq e hep heq
  have hp' : (p.map (induceVal G _)).IsCycle :=
    (Walk.isCycle_map_iff_of_injective induceVal_injective).mpr hp
  have hq' : (q.map (induceVal G _)).IsCycle :=
    (Walk.isCycle_map_iff_of_injective induceVal_injective).mpr hq
  have hep' : Sym2.map (induceVal G _) e ∈ (p.map (induceVal G _)).edges := by
    rw [Walk.edges_map]
    exact List.mem_map_of_mem hep
  have heq' : Sym2.map (induceVal G _) e ∈ (q.map (induceVal G _)).edges := by
    rw [Walk.edges_map]
    exact List.mem_map_of_mem heq
  have heqsets := hG.2 _ _ hp' hq' _ hep' heq'
  rw [edges_toFinset_map, edges_toFinset_map] at heqsets
  exact Finset.image_injective (Sym2.map.injective induceVal_injective) heqsets

/-- **The cut-vertex split** (handoff §6.5): a vertex of degree at least three in a cactus splits
it into two cacti meeting only there, with the root on the side one asks for.

The two sides are the component `S` of one neighbour of `u` in `G - u`, extended by `u`, and
everything else. No edge crosses, because an edge between the sides away from `u` would carry
membership of `S` across it. Both sides are connected: inside `S` a walk of `G - u` never leaves
`S`, and `u` hangs on it through that neighbour; outside, a walk towards `u` can never enter `S`,
one edge at a time. Both inherit the cycle condition along `induceVal`. -/
theorem exists_cut_split_of_three_le_degree (hG : IsCactus G) {u : V} (hu : 3 ≤ G.degree u)
    (r : V) :
    ∃ (u : V) (A B : Set V) (dA : DecidablePred (· ∈ A)) (dB : DecidablePred (· ∈ B)),
      letI := dA; letI := dB;
      (r ∈ A ∧ u ∈ A ∧ u ∈ B ∧
        (∀ v : V, v ∈ A ∨ v ∈ B) ∧ (∀ v : V, v ∈ A → v ∈ B → v = u) ∧
        (∀ x y : V, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)) ∧
        (∃ a ∈ A, a ≠ u) ∧ (∃ b ∈ B, b ≠ u) ∧
        IsCactus (G.induce A) ∧ IsCactus (G.induce B)) := by
  classical
  obtain ⟨x, y, hxu, hyu, hax, hay, hnr⟩ := exists_nonreachable_adj_of_three_le_degree hG hu
  -- `S` is the component of `x` once `u` is deleted
  set D : Set V := {w : V | w ≠ u} with hD
  set S : Set V := {v : V | ∃ h : v ∈ D, (G.induce D).Reachable ⟨x, hxu⟩ ⟨v, h⟩} with hSdef
  have hxS : x ∈ S := ⟨hxu, Reachable.refl _⟩
  have hyS : y ∉ S := fun ⟨h, hre⟩ => hnr hre
  have hSne : ∀ v, v ∈ S → v ≠ u := fun v hv => hv.1
  -- membership of `S` is transported along edges away from `u`
  have hSadj : ∀ p q : V, G.Adj p q → p ≠ u → q ≠ u → p ∈ S → q ∈ S := by
    rintro p q hpq hpu hqu ⟨hpD, hre⟩
    exact ⟨hqu, Reachable.trans hre
      (Adj.reachable (show (G.induce D).Adj ⟨p, hpu⟩ ⟨q, hqu⟩ from hpq))⟩
  -- the two sides
  set A₀ : Set V := {v : V | v ∈ S ∨ v = u} with hA₀
  set B₀ : Set V := {v : V | v ∉ S} with hB₀
  let dA : DecidablePred (· ∈ A₀) := Classical.decPred _
  let dB : DecidablePred (· ∈ B₀) := Classical.decPred _
  have huA : u ∈ A₀ := Or.inr rfl
  have huB : u ∈ B₀ := fun h => hSne u h rfl
  have hcover : ∀ v : V, v ∈ A₀ ∨ v ∈ B₀ := by
    intro v
    by_cases hv : v ∈ S
    · exact Or.inl (Or.inl hv)
    · exact Or.inr hv
  have hmeet : ∀ v : V, v ∈ A₀ → v ∈ B₀ → v = u := by
    rintro v (hv | hv) hvB
    · exact absurd hv hvB
    · exact hv
  have hedge : ∀ p q : V, G.Adj p q → (p ∈ A₀ ∧ q ∈ A₀) ∨ (p ∈ B₀ ∧ q ∈ B₀) := by
    intro p q hpq
    by_cases hpu : p = u
    · subst hpu
      by_cases hqS : q ∈ S
      · exact Or.inl ⟨huA, Or.inl hqS⟩
      · exact Or.inr ⟨huB, hqS⟩
    · by_cases hqu : q = u
      · subst hqu
        by_cases hpS : p ∈ S
        · exact Or.inl ⟨Or.inl hpS, huA⟩
        · exact Or.inr ⟨hpS, huB⟩
      · by_cases hpS : p ∈ S
        · exact Or.inl ⟨Or.inl hpS, Or.inl (hSadj p q hpq hpu hqu hpS)⟩
        · exact Or.inr ⟨hpS, fun hqS => hpS (hSadj q p hpq.symm hqu hpu hqS)⟩
  -- the `A` side is connected: every vertex of `S` walks to `x` inside `S`, and `x` meets `u`
  have hAconn : (G.induce A₀).Connected := by
    have hkey : ∀ a : A₀, (G.induce A₀).Reachable a ⟨u, huA⟩ := by
      rintro ⟨v, hv | hv⟩
      · -- inside the component
        obtain ⟨hvD, hre⟩ := hv
        obtain ⟨W⟩ := hre.symm
        have hsupp : ∀ w ∈ W.support, w.val ∈ A₀ := by
          -- every vertex of a walk out of `v` stays in the component
          have hgen : ∀ (a b : D) (W' : (G.induce D).Walk a b), a.val ∈ S →
              ∀ w ∈ W'.support, w.val ∈ S := by
            intro a b W'
            induction W' with
            | nil =>
              intro ha w hw
              simp only [Walk.support_nil, List.mem_singleton] at hw
              exact hw ▸ ha
            | @cons c d e hadj p ih =>
              intro ha w hw
              rw [Walk.support_cons, List.mem_cons] at hw
              rcases hw with rfl | hw
              · exact ha
              · exact ih (hSadj c.val d.val hadj c.2 d.2 ha) w hw
          exact fun w hw => Or.inl (hgen ⟨v, hvD⟩ ⟨x, hxu⟩ W ⟨hvD, hre⟩ w hw)
        obtain ⟨W'⟩ := exists_walk_induce_of_support W (Or.inl ⟨hvD, hre⟩) (Or.inl hxS) hsupp
        exact Reachable.trans ⟨W'⟩
          (Adj.reachable (show (G.induce A₀).Adj ⟨x, Or.inl hxS⟩ ⟨u, huA⟩ from hax.symm))
      · subst hv
        exact Reachable.refl _
    rw [connected_iff]
    exact ⟨fun a b => (hkey a).trans (hkey b).symm, ⟨⟨u, huA⟩⟩⟩
  -- the `B` side is connected: follow any walk to `u`; it can never enter the component
  have hBconn : (G.induce B₀).Connected := by
    have hgen : ∀ (v w : V) (W : G.Walk v w), w = u → ∀ (hv : v ∈ B₀),
        (G.induce B₀).Reachable ⟨v, hv⟩ ⟨u, huB⟩ := by
      intro v w W
      induction W with
      | nil =>
        intro hwu hv
        subst hwu
        exact Reachable.refl _
      | @cons a c b hadj p ih =>
        intro hbu ha
        by_cases hau : a = u
        · subst hau
          exact Reachable.refl _
        · by_cases hcu : c = u
          · subst hcu
            exact Adj.reachable (show (G.induce B₀).Adj ⟨a, ha⟩ ⟨c, huB⟩ from hadj)
          · have hcB : c ∈ B₀ := fun hcS => ha (hSadj c a hadj.symm hcu hau hcS)
            exact (Adj.reachable
              (show (G.induce B₀).Adj ⟨a, ha⟩ ⟨c, hcB⟩ from hadj)).trans (ih hbu hcB)
    have hkey : ∀ a : B₀, (G.induce B₀).Reachable a ⟨u, huB⟩ := by
      rintro ⟨v, hv⟩
      obtain ⟨W⟩ := hG.1.preconnected v u
      exact hgen v u W rfl hv
    rw [connected_iff]
    exact ⟨fun a b => (hkey a).trans (hkey b).symm, ⟨⟨u, huB⟩⟩⟩
  have hcactA : IsCactus (G.induce A₀) := ⟨hAconn, isCactus_edges_induce hG A₀⟩
  have hcactB : IsCactus (G.induce B₀) := ⟨hBconn, isCactus_edges_induce hG B₀⟩
  by_cases hr : r ∈ A₀
  · exact ⟨u, A₀, B₀, dA, dB, hr, huA, huB, hcover, hmeet, hedge,
      ⟨x, Or.inl hxS, hxu⟩, ⟨y, hyS, hyu⟩, hcactA, hcactB⟩
  · exact ⟨u, B₀, A₀, dB, dA, (hcover r).resolve_left hr, huB, huA,
      fun v => (hcover v).symm, fun v hvB hvA => hmeet v hvA hvB,
      fun p q h => (hedge p q h).symm, ⟨y, hyS, hyu⟩, ⟨x, Or.inl hxS, hxu⟩, hcactB, hcactA⟩

/-- **A pendant vertex splits a cactus**: its edge on one side, everything else on the other. -/
theorem exists_leaf_cut_split (hG : IsCactus G) {x : V} (hdeg : G.degree x = 1)
    (hcard : 3 ≤ Fintype.card V) (r : V) :
    ∃ (u : V) (A B : Set V) (dA : DecidablePred (· ∈ A)) (dB : DecidablePred (· ∈ B)),
      letI := dA; letI := dB;
      (r ∈ A ∧ u ∈ A ∧ u ∈ B ∧
        (∀ v : V, v ∈ A ∨ v ∈ B) ∧ (∀ v : V, v ∈ A → v ∈ B → v = u) ∧
        (∀ p q : V, G.Adj p q → (p ∈ A ∧ q ∈ A) ∨ (p ∈ B ∧ q ∈ B)) ∧
        (∃ a ∈ A, a ≠ u) ∧ (∃ b ∈ B, b ≠ u) ∧
        IsCactus (G.induce A) ∧ IsCactus (G.induce B)) := by
  classical
  obtain ⟨u, hxu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hux : u ≠ x := hxu.ne'
  set E : Set V := {v : V | v = x ∨ v = u} with hE
  set C : Set V := {v : V | v ≠ x} with hC
  have huE : u ∈ E := Or.inr rfl
  have hxE : x ∈ E := Or.inl rfl
  have huC : u ∈ C := hux
  have hcover : ∀ v : V, v ∈ E ∨ v ∈ C := by
    intro v
    by_cases hv : v = x
    · exact Or.inl (Or.inl hv)
    · exact Or.inr hv
  have hmeet : ∀ v : V, v ∈ E → v ∈ C → v = u := by
    rintro v (hv | hv) hvC
    · exact absurd hv hvC
    · exact hv
  have hedge : ∀ p q : V, G.Adj p q → (p ∈ E ∧ q ∈ E) ∨ (p ∈ C ∧ q ∈ C) := by
    intro p q hpq
    by_cases hp : p = x
    · subst hp
      exact Or.inl ⟨hxE, Or.inr (huniq q hpq)⟩
    · by_cases hq : q = x
      · subst hq
        exact Or.inl ⟨Or.inr (huniq p hpq.symm), hxE⟩
      · exact Or.inr ⟨hp, hq⟩
  -- a third vertex lies outside the leaf edge
  have hthird : ∃ b : V, b ≠ x ∧ b ≠ u := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset V) ⊆ {x, u} := by
      intro v _
      rcases eq_or_ne v x with rfl | hv
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hcon v hv))
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h2 : ({x, u} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    omega
  obtain ⟨b, hbx, hbu⟩ := hthird
  let dE : DecidablePred (· ∈ E) := Classical.decPred _
  let dC : DecidablePred (· ∈ C) := Classical.decPred _
  -- the leaf edge is a two-vertex cactus
  have hEcard : Fintype.card E < 3 := by
    have hsub : (Set.toFinset E) ⊆ ({x, u} : Finset V) := by
      intro v hv
      rw [Set.mem_toFinset] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h2 : ({x, u} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have := Finset.card_le_card hsub
    rw [Set.toFinset_card] at this
    omega
  have hEcact : IsCactus (G.induce E) := by
    refine ⟨?_, fun a b p q hp _ _ _ _ => absurd hp (not_isCycle_of_card_lt_three hEcard)⟩
    rw [connected_iff]
    refine ⟨fun a b => ?_, ⟨⟨u, huE⟩⟩⟩
    have hstep : ∀ c : E, (G.induce E).Reachable c ⟨u, huE⟩ := by
      rintro ⟨v, hv | hv⟩
      · subst hv
        exact Adj.reachable (show (G.induce E).Adj ⟨v, Or.inl rfl⟩ ⟨u, huE⟩ from hxu)
      · subst hv
        exact Reachable.refl _
    exact (hstep a).trans (hstep b).symm
  have hCcact : IsCactus (G.induce C) :=
    ⟨connected_induce_of_degree_eq_one hG.1 hdeg ⟨u, hux⟩, isCactus_edges_induce hG C⟩
  by_cases hr : r ∈ C
  · exact ⟨u, C, E, dC, dE, hr, huC, huE, fun v => (hcover v).symm,
      fun v hvC hvE => hmeet v hvE hvC, fun p q h => (hedge p q h).symm,
      ⟨b, hbx, hbu⟩, ⟨x, hxE, hux.symm⟩, hCcact, hEcact⟩
  · have hrx : r = x := by
      by_contra hne
      exact hr hne
    exact ⟨u, E, C, dE, dC, hrx ▸ hxE, huE, huC, hcover, hmeet, hedge,
      ⟨x, hxE, hux.symm⟩, ⟨b, hbx, hbu⟩, hEcact, hCcact⟩

end ListColoring
