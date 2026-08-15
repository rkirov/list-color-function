/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Structure

/-!
# Leaf peeling: the core of a connected graph with at most one cycle

The reverse `k = 2` direction (handoff §3): a connected graph with at most one cycle has a
vertex core or a cycle core. The induction peels degree-one vertices; this file builds the
pieces: cycles restrict to induced subgraphs, paths between surviving vertices avoid a leaf,
connectivity survives leaf deletion, and the leaf-deletion isomorphism.
-/

namespace ListColoring

open SimpleGraph

set_option linter.unusedSectionVars false

section InduceTransport

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- The inclusion homomorphism of an induced subgraph. -/
def induceVal (G : SimpleGraph V) (s : Set V) : G.induce s →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

theorem induceVal_injective {s : Set V} : Function.Injective (induceVal G s) :=
  Subtype.val_injective

/-- At most one cycle passes to induced subgraphs. -/
theorem HasAtMostOneCycle.induce (h : HasAtMostOneCycle G) (s : Set V) :
    HasAtMostOneCycle (G.induce s) := by
  intro u v p q hp hq
  have hp' : (p.map (induceVal G s)).IsCycle :=
    (Walk.isCycle_map_iff_of_injective induceVal_injective).mpr hp
  have hq' : (q.map (induceVal G s)).IsCycle :=
    (Walk.isCycle_map_iff_of_injective induceVal_injective).mpr hq
  have heq := h _ _ hp' hq'
  rw [edges_toFinset_map, edges_toFinset_map] at heq
  exact Finset.image_injective (Sym2.map.injective induceVal_injective) heq

/-- A walk avoiding `x` restricts to the induced complement of `x`. -/
theorem exists_induce_walk_of_notMem_support {x a b : V}
    (W : G.Walk a b) : ∀ (ha : a ≠ x) (hb : b ≠ x), x ∉ W.support →
    Nonempty ((G.induce {y | y ≠ x}).Walk ⟨a, ha⟩ ⟨b, hb⟩) := by
  induction W with
  | nil =>
    intro ha _ _
    exact ⟨Walk.nil⟩
  | @cons u y z hadj p ih =>
    intro ha hb hW
    have hy : y ≠ x := by
      intro hyx
      exact hW (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ (hyx ▸ p.start_mem_support))
    have hp : x ∉ p.support := fun hmem =>
      hW (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hmem)
    obtain ⟨p'⟩ := ih hy hb hp
    exact ⟨Walk.cons (by exact hadj) p'⟩

end InduceTransport

section LeafAvoidance

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **A path between two survivors avoids a leaf.** If a path visited the degree-one vertex
`x` internally, the step into `x` and the step out of `x` would give two distinct neighbours. -/
theorem notMem_support_of_isPath_of_degree_eq_one {x a b : V} (hdeg : G.degree x = 1)
    (ha : a ≠ x) (hb : b ≠ x) {W : G.Walk a b} (hW : W.IsPath) : x ∉ W.support := by
  intro hmem
  have hn1 : ¬ (W.takeUntil x hmem).Nil := Walk.not_nil_of_ne ha
  have hn2 : ¬ (W.dropUntil x hmem).Nil := Walk.not_nil_of_ne (Ne.symm hb)
  have hin : G.Adj (W.takeUntil x hmem).penultimate x :=
    (W.takeUntil x hmem).adj_penultimate hn1
  have hout : G.Adj x (W.dropUntil x hmem).snd :=
    (W.dropUntil x hmem).adj_snd hn2
  obtain ⟨w, hw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  have he1 : (W.takeUntil x hmem).penultimate = w := huniq _ hin.symm
  have he2 : (W.dropUntil x hmem).snd = w := huniq _ hout
  have hmem1 : w ∈ (W.takeUntil x hmem).support := by
    rw [← he1]
    exact (W.takeUntil x hmem).getVert_mem_support _
  have hmem2 : w ∈ (W.dropUntil x hmem).support.tail := by
    have hs := (W.dropUntil x hmem).support_eq_cons
    have hsnd : (W.dropUntil x hmem).snd ∈ (W.dropUntil x hmem).support :=
      (W.dropUntil x hmem).getVert_mem_support _
    rw [hs] at hsnd
    rcases List.mem_cons.mp hsnd with h | h
    · exact absurd rfl (h ▸ hout).ne
    · exact he2 ▸ h
  have hsplit : W.support =
      (W.takeUntil x hmem).support ++ (W.dropUntil x hmem).support.tail :=
    (congrArg Walk.support (W.take_spec hmem)).symm.trans (Walk.support_append _ _)
  have hnodup := hW.support_nodup
  rw [hsplit] at hnodup
  exact ((List.nodup_append.mp hnodup).2.2 w hmem1 w hmem2) rfl

end LeafAvoidance

section LeafDeletion

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Connectivity survives leaf deletion**: paths between survivors avoid the leaf. -/
theorem connected_induce_of_degree_eq_one {x : V} (hconn : G.Connected)
    (hdeg : G.degree x = 1) (hne : ∃ y : V, y ≠ x) :
    (G.induce {y | y ≠ x}).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨W⟩ := hconn.preconnected a b
    have hx : x ∉ (W.toPath : G.Walk a b).support :=
      notMem_support_of_isPath_of_degree_eq_one hdeg ha hb W.toPath.2
    obtain ⟨w⟩ := exists_induce_walk_of_notMem_support _ ha hb hx
    exact ⟨w⟩
  · obtain ⟨y, hy⟩ := hne
    exact ⟨⟨y, hy⟩⟩

/-- The vertex equivalence deleting `x`: `Option {y // y ≠ x} ≃ V`. -/
def delOptionEquiv (x : V) : Option {y : V // y ≠ x} ≃ V where
  toFun := fun o => o.elim x Subtype.val
  invFun := fun v => if h : v = x then none else some ⟨v, h⟩
  left_inv := by
    rintro (_ | ⟨y, hy⟩)
    · simp
    · simp [hy]
  right_inv := by
    intro v
    by_cases h : v = x <;> simp [h]

/-- **The leaf-deletion isomorphism**: a graph with a degree-one vertex `x`, whose unique
neighbour is `w`, is its induced complement of `x` with a pendant added back at `w`. -/
def leafIso {x w : V} (hxw : G.Adj x w) (huniq : ∀ y, G.Adj x y → y = w) (hw : w ≠ x) :
    G ≃g (G.induce {y | y ≠ x}).addPendant ⟨w, hw⟩ where
  toEquiv := (delOptionEquiv x).symm
  map_rel_iff' := by
    intro a b
    have hnone : (delOptionEquiv x).symm x = none := by simp [delOptionEquiv]
    have hsome : ∀ (v : V) (hv : v ≠ x), (delOptionEquiv x).symm v = some ⟨v, hv⟩ := by
      intro v hv; simp [delOptionEquiv, hv]
    show ((G.induce {y | y ≠ x}).addPendant ⟨w, hw⟩).Adj
        ((delOptionEquiv x).symm a) ((delOptionEquiv x).symm b) ↔ G.Adj a b
    by_cases ha : a = x <;> by_cases hb : b = x
    · rw [ha, hb, hnone]
      exact iff_of_false (fun h => h) (fun h => absurd rfl h.ne)
    · rw [ha, hnone, hsome b hb]
      show (⟨b, hb⟩ : {y // y ≠ x}) = ⟨w, hw⟩ ↔ G.Adj x b
      constructor
      · intro h
        obtain rfl : b = w := congrArg Subtype.val h
        exact hxw
      · intro h
        exact Subtype.ext (huniq b h)
    · rw [hb, hnone, hsome a ha]
      show (⟨a, ha⟩ : {y // y ≠ x}) = ⟨w, hw⟩ ↔ G.Adj a x
      constructor
      · intro h
        obtain rfl : a = w := congrArg Subtype.val h
        exact hxw.symm
      · intro h
        exact Subtype.ext (huniq a h.symm)
    · rw [hsome a ha, hsome b hb]
      exact Iff.rfl

/-- `addPendant` congruence under isomorphism. -/
def addPendantCongr {U U' : Type} {H : SimpleGraph U} {H' : SimpleGraph U'} (f : H ≃g H')
    (w : U) : H.addPendant w ≃g H'.addPendant (f w) where
  toEquiv := Equiv.optionCongr f.toEquiv
  map_rel_iff' := by
    rintro (_ | a) (_ | b)
    · exact Iff.rfl
    · show (f b = f w) ↔ (b = w)
      exact ⟨fun h => f.toEquiv.injective h, fun h => congrArg f h⟩
    · show (f a = f w) ↔ (a = w)
      exact ⟨fun h => f.toEquiv.injective h, fun h => congrArg f h⟩
    · exact f.map_rel_iff

end LeafDeletion

section Gluing

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- **Gluing two internally disjoint, edge-disjoint paths into a cycle.** -/
theorem isCycle_append_of_isPath {a b : V} {p : G.Walk a b} {q : G.Walk b a}
    (hp : p.IsPath) (hq : q.IsPath) (hab : a ≠ b)
    (hint : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b)
    (hedges : ∀ e ∈ p.edges, e ∉ q.edges) : (p.append q).IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [Walk.edges_append]
    exact List.nodup_append.mpr ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup,
      fun e he e' he' => fun h => hedges e he (h ▸ he')⟩
  · intro h
    have hlen := congrArg Walk.length h
    rw [Walk.length_append] at hlen
    have hp1 : 0 < p.length := by
      rcases Nat.eq_zero_or_pos p.length with h0 | h0
      · exact absurd (Walk.eq_of_length_eq_zero h0) hab
      · exact h0
    simp only [Walk.length_nil] at hlen
    omega
  · have hsupp : (p.append q).support = p.support ++ q.support.tail :=
      Walk.support_append p q
    have hps : p.support = a :: p.support.tail := p.support_eq_cons
    have htail : (p.append q).support.tail = p.support.tail ++ q.support.tail := by
      rw [hsupp, hps]
      rfl
    rw [htail]
    refine List.nodup_append.mpr ⟨(List.tail_sublist _).nodup hp.support_nodup,
      (List.tail_sublist _).nodup hq.support_nodup, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have hx' : x ∈ p.support := List.mem_of_mem_tail hx
    have hy' : x ∈ q.support := List.mem_of_mem_tail hy
    rcases hint x hx' hy' with rfl | rfl
    · have : x ∉ p.support.tail := by
        have hnodup := hp.support_nodup
        rw [hps] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact this hx
    · have : x ∉ q.support.tail := by
        have hnodup := hq.support_nodup
        rw [q.support_eq_cons] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact this hy

end Gluing

section Endgame

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **In a connected graph with at most one cycle and minimum degree two, every edge lies on
the cycle.** Otherwise Rubin's connecting path plus an arc of the cycle glues into a second
cycle whose edge set differs. -/
theorem forall_edge_mem_of_hasAtMostOneCycle (hconn : G.Connected)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) (h1 : HasAtMostOneCycle G)
    {v₀ : V} {c : G.Walk v₀ v₀} (hc : c.IsCycle) :
    ∀ x y, G.Adj x y → s(x, y) ∈ c.edges := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, y, hxy, hnot⟩ := hcon
  have hcycmeet : ∀ (z : V) (d : G.Walk z z), d.IsCycle →
      ∃ s ∈ d.support, ∃ t ∈ d.support, s ∈ c.support ∧ t ∈ c.support ∧ s ≠ t := by
    intro z d hd
    have hne : d.edges ≠ [] := by
      intro h
      have h3 := hd.three_le_length
      have h4 := d.length_edges
      rw [h] at h4
      simp at h4
      omega
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    have hec : e ∈ c.edges := by
      have heq := h1 d c hd hc
      have h4 : e ∈ d.edges.toFinset := List.mem_toFinset.mpr he
      rw [heq] at h4
      exact List.mem_toFinset.mp h4
    revert he hec
    induction e using Sym2.ind with
    | _ s t =>
      intro he hec
      exact ⟨s, d.fst_mem_support_of_mem_edges he, t, d.snd_mem_support_of_mem_edges he,
        c.fst_mem_support_of_mem_edges hec, c.snd_mem_support_of_mem_edges hec,
        (d.adj_of_mem_edges he).ne⟩
  obtain ⟨a, b, p, hac, hbc, hab, hp, hlen, hint, hpedges⟩ :=
    exists_connecting_path_of_cycle hconn hdeg ⟨x, y, hxy, hnot⟩ hcycmeet
  have hamem : a ∈ (c.rotate b hbc).support :=
    ((c.mem_support_rotate_iff b hbc).mpr hac : _)
  set arc := (c.rotate b hbc).takeUntil a hamem with harc
  have harc_path : arc.IsPath := (hc.rotate hbc).isPath_takeUntil hamem
  have harc_supp : ∀ z, z ∈ arc.support → z ∈ c.support := fun z hz =>
    (c.mem_support_rotate_iff b hbc).mp
      ((c.rotate b hbc).support_takeUntil_subset hamem hz)
  have harc_edges : ∀ e, e ∈ arc.edges → e ∈ c.edges := fun e he =>
    (c.rotate_edges b hbc).perm.mem_iff.mp
      ((c.rotate b hbc).edges_takeUntil_subset_edges hamem he)
  have hglue : (p.append arc).IsCycle := by
    apply isCycle_append_of_isPath hp harc_path hab
    · intro z hz hz'
      by_contra hcontra
      push_neg at hcontra
      exact (hint z hz hcontra.1 hcontra.2) (harc_supp z hz')
    · intro e he he'
      exact hpedges e he (harc_edges e he')
  -- the glued cycle contains an off-`c` edge, contradicting at-most-one-cycle
  have hpne : ¬ p.Nil := Walk.not_nil_of_ne hab
  have hfirst : s(a, p.snd) ∈ p.edges := by
    have h2 : (p.firstDart hpne) ∈ p.darts := Walk.firstDart_mem_darts hpne
    rw [← p.edge_firstDart hpne]
    exact List.mem_map_of_mem h2
  have hmem_glue : s(a, p.snd) ∈ (p.append arc).edges := by
    rw [Walk.edges_append]
    exact List.mem_append_left _ hfirst
  have heq := h1 _ c hglue hc
  have : s(a, p.snd) ∈ c.edges := by
    have h4 : s(a, p.snd) ∈ (p.append arc).edges.toFinset :=
      List.mem_toFinset.mpr hmem_glue
    rw [heq] at h4
    exact List.mem_toFinset.mp h4
  exact hpedges _ hfirst this


/-- Every vertex lies on the cycle, once every edge does. -/
theorem forall_mem_support_of_forall_edge_mem (hdeg : ∀ v : V, 2 ≤ G.degree v)
    {v₀ : V} {c : G.Walk v₀ v₀}
    (hall : ∀ x y, G.Adj x y → s(x, y) ∈ c.edges) (v : V) : v ∈ c.support := by
  have hpos : 0 < G.degree v := lt_of_lt_of_le Nat.zero_lt_two (hdeg v)
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hpos
  exact c.fst_mem_support_of_mem_edges (hall v w hw)

/-- **The cycle-core construction**: a connected graph with minimum degree two whose edges and
vertices all lie on one cycle `c` is isomorphic to `closePath (c.length - 1)`.

The isomorphism indexes vertices along the cycle: `getVert` is injective on `[0, length)`
(`cycleWalk_injOn`), surjective by the support hypothesis, and maps the cycle adjacency to the
index adjacency of `ListColoring.closePath_adj_pathVtx_fin`. -/
theorem coreIsCycle_of_forall_edge_mem (hconn : G.Connected)
    (hdeg : ∀ v : V, 2 ≤ G.degree v) {v₀ : V} {c : G.Walk v₀ v₀} (hc : c.IsCycle)
    (hall : ∀ x y, G.Adj x y → s(x, y) ∈ c.edges) : CoreIsCycle G := by
  sorry

end Endgame

section Peeling

/-- `CoreIs` extends through an added pendant. -/
theorem coreIs_addPendant {V U W' : Type} [Fintype V] [DecidableEq V] [Fintype U]
    [DecidableEq U] [Fintype W'] [DecidableEq W'] {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : SimpleGraph U} [DecidableRel H.Adj] {K : SimpleGraph W'} [DecidableRel K.Adj] {w : U}
    (e : G ≃g H.addPendant w) (h : CoreIs H K) : CoreIs G K := by
  obtain ⟨k, d, ⟨f⟩⟩ := h
  exact ⟨k + 1, (d, f w), ⟨e.trans (addPendantCongr f w)⟩⟩

/-- One-vertex graphs have vertex cores. -/
theorem coreIsVertex_of_card_eq_one {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : Fintype.card V = 1) : CoreIsVertex G := by
  refine ⟨0, PUnit.unit, ⟨?_⟩⟩
  have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have e : V ≃ PathV 0 := Fintype.equivOfCardEq (by rw [h]; rfl)
  exact ⟨e, by
    intro a b
    refine iff_of_false (fun hadj => hadj) (fun hadj => ?_)
    have : a = b := Subsingleton.elim a b
    exact absurd this hadj.ne⟩

/-- **Leaf peeling**: a connected graph with at most one cycle has a vertex core or a cycle
core. The minimum-degree-two endgame is the cycle case. -/
theorem coreIsVertex_or_coreIsCycle :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → G.Connected → HasAtMostOneCycle G →
      CoreIsVertex G ∨ CoreIsCycle G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ G _ hcard hconn h1
    by_cases hleaf : ∃ x, G.degree x = 1
    · obtain ⟨x, hdeg⟩ := hleaf
      obtain ⟨w, hw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
      letI : DecidableRel (G.induce {y | y ≠ x}).Adj :=
        fun a b => inferInstanceAs (Decidable (G.Adj a b))
      have hcards : Fintype.card {y : V // y ≠ x} + 1 = n := by
        have hc := Fintype.card_congr (delOptionEquiv x)
        rw [Fintype.card_option] at hc
        omega
      have hlt : Fintype.card {y : V // y ≠ x} < n := by omega
      have hG' := IH _ hlt {y : V // y ≠ x} (G.induce {y | y ≠ x}) rfl
        (connected_induce_of_degree_eq_one hconn hdeg ⟨w, hw.ne'⟩) (h1.induce _)
      have e := leafIso hw huniq hw.ne'
      rcases hG' with h | h
      · exact Or.inl (coreIs_addPendant e h)
      · obtain ⟨k, hk, hcore⟩ := h
        exact Or.inr ⟨k, hk, coreIs_addPendant e hcore⟩
    · push_neg at hleaf
      by_cases hone : Fintype.card V = 1
      · exact Or.inl (coreIsVertex_of_card_eq_one hone)
      · -- no leaves, at least two vertices: minimum degree two, and `G` is its one cycle
        have hnontriv : Nontrivial V := by
          have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
          exact Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        have hdeg : ∀ v : V, 2 ≤ G.degree v := by
          intro v
          obtain ⟨u, hu⟩ := exists_ne v
          obtain ⟨W⟩ := hconn.preconnected v u
          have hnil : ¬ W.Nil := Walk.not_nil_of_ne (Ne.symm hu)
          have hadj : G.Adj v W.snd := W.adj_snd hnil
          have hpos : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨_, hadj⟩
          have hne1 : G.degree v ≠ 1 := hleaf v
          omega
        obtain ⟨v₀, c, hc⟩ := exists_isCycle_of_two_le_degree hconn hdeg
        exact Or.inr (coreIsCycle_of_forall_edge_mem hconn hdeg hc
          (forall_edge_mem_of_hasAtMostOneCycle hconn hdeg h1 hc))



end Peeling

end ListColoring
