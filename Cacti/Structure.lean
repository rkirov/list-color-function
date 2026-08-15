/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Defs

/-!
# Cactus structure theory

The graph-structure layer of the cactus classification (handoff §3, §10 "Cactus structure").
Everything here is about cycles, pendant vertices, and cores — no list coloring.

The two directions of the `k = 2` classification need:

* **Transport**: cycles of `G` correspond to cycles of its core — the pendant vertex lies on no
  cycle (`not_mem_support_of_isCycle_addPendant`), so cycles descend
  (`exists_map_of_isCycle_addPendant`) and lift along the canonical embedding; both compose up
  a pendant tower and across an isomorphism.
* **Structure**: a connected graph with at most one cycle has a vertex or cycle core, by leaf
  peeling; the concrete cycle-graph rigidity; and the two shared-edge cycles of `θ₁ = K₂,₃`.
-/

namespace ListColoring

open SimpleGraph

set_option linter.unusedSectionVars false

section Pendant

variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {v : V}

/-- The canonical embedding of `G` into `G.addPendant v`. -/
def somePendantHom (G : SimpleGraph V) (v : V) : G →g G.addPendant v where
  toFun := some
  map_rel' := fun h => h

omit [DecidableEq V] in
theorem somePendantHom_injective : Function.Injective (somePendantHom G v) :=
  Option.some_injective V

/-- **The pendant vertex lies on no cycle.** Its unique neighbour would have to be both the
second and the second-to-last vertex of the cycle. -/
theorem not_mem_support_of_isCycle_addPendant {u : Option V}
    {c : (G.addPendant v).Walk u u} (hc : c.IsCycle) : none ∉ c.support := by
  intro hmem
  have hcyc' : (c.rotate none hmem).IsCycle := hc.rotate hmem
  have hnil : ¬ (c.rotate none hmem).Nil := hcyc'.not_nil
  have hsnd : (c.rotate none hmem).snd = some v := by
    have hadj := (c.rotate none hmem).adj_snd hnil
    match h : (c.rotate none hmem).snd with
    | none => rw [h] at hadj; exact absurd rfl hadj.ne
    | some b =>
      rw [h] at hadj
      have hb : b = v := hadj
      rw [hb]
  have hpen : (c.rotate none hmem).penultimate = some v := by
    have hadj := (c.rotate none hmem).adj_penultimate hnil
    match h : (c.rotate none hmem).penultimate with
    | none => rw [h] at hadj; exact absurd rfl hadj.ne
    | some b =>
      rw [h] at hadj
      have hb : b = v := hadj
      rw [hb]
  exact hcyc'.snd_ne_penultimate (hsnd.trans hpen.symm)

/-- A walk of `G.addPendant v` avoiding the pendant vertex is the image of a walk of `G` under
the canonical embedding, up to endpoint `copy`. -/
theorem exists_map_of_notMem_support {x y : Option V}
    (c : (G.addPendant v).Walk x y) (h : none ∉ c.support) :
    ∃ (a b : V) (ha : x = some a) (hb : y = some b) (c' : G.Walk a b),
      c.copy ha hb = c'.map (somePendantHom G v) := by
  induction c with
  | nil =>
    rename_i x
    cases x with
    | none => exact absurd (Walk.start_mem_support _) h
    | some a => exact ⟨a, a, rfl, rfl, Walk.nil, rfl⟩
  | cons hadj p ih =>
    rename_i x w y
    cases x with
    | none => exact absurd (Walk.start_mem_support _) h
    | some a =>
      have hw : none ∉ p.support := by
        rw [Walk.support_cons] at h
        exact fun hh => h (List.mem_cons_of_mem _ hh)
      obtain ⟨a', b, hwa, hyb, p', hp'⟩ := ih hw
      subst hwa
      have hG : G.Adj a a' := hadj
      refine ⟨a, b, rfl, hyb, Walk.cons hG p', ?_⟩
      rw [Walk.copy_cons, Walk.map_cons, hp']
      rfl

/-- **Cycles of `G.addPendant v` are images of cycles of `G`.** -/
theorem exists_map_of_isCycle_addPendant {u : Option V} {c : (G.addPendant v).Walk u u}
    (hc : c.IsCycle) :
    ∃ (a : V) (ha : u = some a) (c' : G.Walk a a),
      c.copy ha ha = c'.map (somePendantHom G v) ∧ c'.IsCycle := by
  obtain ⟨a, b, ha, hb, c', hc'⟩ :=
    exists_map_of_notMem_support c (not_mem_support_of_isCycle_addPendant hc)
  obtain rfl : a = b := by
    have := ha.symm.trans hb
    exact Option.some_injective V this
  refine ⟨a, ha, c', hc', ?_⟩
  have hcopy : (c.copy ha ha).IsCycle := by
    subst ha; simpa using hc
  rw [hc'] at hcopy
  exact (Walk.isCycle_map_iff_of_injective somePendantHom_injective).mp hcopy

/-- Cycles of `G` lift to cycles of `G.addPendant v` along the canonical embedding. -/
theorem isCycle_map_addPendant {a : V} {c : G.Walk a a} (hc : c.IsCycle) :
    (c.map (somePendantHom G v)).IsCycle :=
  (Walk.isCycle_map_iff_of_injective somePendantHom_injective).mpr hc

end Pendant

section EdgesToFinset

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- Edge sets of mapped walks are images of edge sets. -/
theorem edges_toFinset_map {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G')
    {u v : V} (p : G.Walk u v) :
    (p.map f).edges.toFinset = p.edges.toFinset.image (Sym2.map f) := by
  ext e
  rw [List.mem_toFinset, Finset.mem_image, Walk.edges_map, List.mem_map]
  constructor
  · rintro ⟨e₁, he₁, rfl⟩; exact ⟨e₁, List.mem_toFinset.mpr he₁, rfl⟩
  · rintro ⟨e₁, he₁, rfl⟩; exact ⟨e₁, List.mem_toFinset.mp he₁, rfl⟩

end EdgesToFinset

section Tower

variable {V : Type} [DecidableEq V] {H : SimpleGraph V}

/-- The function embedding the base vertices into the tower vertex type. -/
def towerInj (V : Type) : (k : ℕ) → V → TowerV V k
  | 0 => id
  | k + 1 => some ∘ towerInj V k

/-- The graph embedding of the base graph into a pendant tower over it. -/
def towerHom (H : SimpleGraph V) : (k : ℕ) → (d : TowerData V k) → H →g pendantTower H k d
  | 0, _ => Hom.id
  | k + 1, ⟨d, w⟩ => (somePendantHom (pendantTower H k d) w).comp (towerHom H k d)

/-- **Cycles of a pendant tower descend to cycles of the base**, with corresponding edge sets. -/
theorem exists_isCycle_base_of_isCycle_pendantTower :
    ∀ (k : ℕ) (d : TowerData V k) {u : TowerV V k} (c : (pendantTower H k d).Walk u u),
      c.IsCycle →
      ∃ (a : V) (c' : H.Walk a a), c'.IsCycle ∧
        c.edges.toFinset = c'.edges.toFinset.image (Sym2.map (towerInj V k))
  | 0, _, u, c, hc =>
      ⟨u, c, hc, by
        ext e
        rw [List.mem_toFinset, Finset.mem_image]
        constructor
        · intro he
          exact ⟨e, List.mem_toFinset.mpr he, congrFun Sym2.map_id e⟩
        · rintro ⟨e', he', rfl⟩
          have h : Sym2.map (towerInj V 0) e' = e' := congrFun Sym2.map_id e'
          rw [h]
          exact List.mem_toFinset.mp he'⟩
  | k + 1, ⟨d, w⟩, u, c, hc => by
      obtain ⟨a, ha, c₁, hcopy, hc₁⟩ := exists_map_of_isCycle_addPendant hc
      obtain ⟨b, c', hc', hedges⟩ :=
        exists_isCycle_base_of_isCycle_pendantTower k d c₁ hc₁
      refine ⟨b, c', hc', ?_⟩
      have s1 : c.edges.toFinset =
          ((c.copy ha ha).edges.toFinset : Finset (Sym2 (TowerV V (k + 1)))) :=
        (congrArg List.toFinset (Walk.edges_copy c ha ha)).symm
      have s2 : ((c.copy ha ha).edges.toFinset : Finset (Sym2 (TowerV V (k + 1)))) =
          ((Walk.map (somePendantHom (pendantTower H k d) w) c₁).edges.toFinset :
            Finset (Sym2 (TowerV V (k + 1)))) :=
        congrArg (fun q => Walk.edges q |>.toFinset) hcopy
      have s3 : ((Walk.map (somePendantHom (pendantTower H k d) w) c₁).edges.toFinset :
            Finset (Sym2 (TowerV V (k + 1)))) =
          (c₁.edges.toFinset.image (Sym2.map (somePendantHom (pendantTower H k d) w)) :
            Finset (Sym2 (TowerV V (k + 1)))) :=
        edges_toFinset_map _ c₁
      have s4 : (c₁.edges.toFinset.image (Sym2.map (somePendantHom (pendantTower H k d) w)) :
            Finset (Sym2 (TowerV V (k + 1)))) =
          ((c'.edges.toFinset.image (Sym2.map (towerInj V k))).image
              (Sym2.map (somePendantHom (pendantTower H k d) w)) :
            Finset (Sym2 (TowerV V (k + 1)))) := by
        rw [hedges]
      have s5 : ((c'.edges.toFinset.image (Sym2.map (towerInj V k))).image
              (Sym2.map (somePendantHom (pendantTower H k d) w)) :
            Finset (Sym2 (TowerV V (k + 1)))) =
          c'.edges.toFinset.image (Sym2.map (towerInj V (k + 1))) := by
        rw [Finset.image_image]
        congr 1
        funext e'
        exact (Sym2.map_map e').trans rfl
      exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- A pendant tower over a graph with at most one cycle has at most one cycle. -/
theorem hasAtMostOneCycle_pendantTower (hH : HasAtMostOneCycle H) (k : ℕ)
    (d : TowerData V k) : HasAtMostOneCycle (pendantTower H k d) := by
  intro u v p q hp hq
  obtain ⟨a, p', hp', hpe⟩ := exists_isCycle_base_of_isCycle_pendantTower k d p hp
  obtain ⟨b, q', hq', hqe⟩ := exists_isCycle_base_of_isCycle_pendantTower k d q hq
  rw [hpe, hqe, hH p' q' hp' hq']

theorem towerHom_injective :
    ∀ (k : ℕ) (d : TowerData V k), Function.Injective (towerHom H k d)
  | 0, _ => fun _ _ h => h
  | k + 1, ⟨d, w⟩ => fun a b h =>
      towerHom_injective k d (Option.some_injective _ h)

/-- **Cycles of the base lift to a pendant tower**, preserving cyclehood; edge sets map along
`towerInj`. -/
theorem isCycle_map_towerHom {k : ℕ} {d : TowerData V k} {a : V} {c : H.Walk a a}
    (hc : c.IsCycle) : (c.map (towerHom H k d)).IsCycle :=
  (Walk.isCycle_map_iff_of_injective (towerHom_injective k d)).mpr hc

end Tower

section IsoTransport

variable {V W : Type} [DecidableEq V] [DecidableEq W]

/-- `HasAtMostOneCycle` transports across an isomorphism. -/
theorem hasAtMostOneCycle_of_iso {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G')
    (h : HasAtMostOneCycle G') : HasAtMostOneCycle G := by
  intro u v p q hp hq
  have hinj : Function.Injective e.toHom := e.toEquiv.injective
  have hp' : (p.map e.toHom).IsCycle :=
    (Walk.isCycle_map_iff_of_injective hinj).mpr hp
  have hq' : (q.map e.toHom).IsCycle :=
    (Walk.isCycle_map_iff_of_injective hinj).mpr hq
  have heq := h _ _ hp' hq'
  rw [edges_toFinset_map, edges_toFinset_map] at heq
  exact Finset.image_injective (Sym2.map.injective hinj) heq

end IsoTransport

section CoreTransport

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- **`HasAtMostOneCycle` descends from the core**: if the core of `G` has at most one cycle,
so does `G`. -/
theorem hasAtMostOneCycle_of_coreIs (h : CoreIs G H) (hH : HasAtMostOneCycle H) :
    HasAtMostOneCycle G := by
  obtain ⟨k, d, ⟨e⟩⟩ := h
  exact hasAtMostOneCycle_of_iso e (hasAtMostOneCycle_pendantTower hH k d)

end CoreTransport


section CactusExclusion

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- **A two-cycle witness in the core refutes cactushood.** If the core has two cycles that
share an edge but have different edge sets, `G` is not a cactus. -/
theorem not_isCactus_of_coreIs_witness (h : CoreIs G H)
    (hw : ∃ (u v : W) (p : H.Walk u u) (q : H.Walk v v), p.IsCycle ∧ q.IsCycle ∧
      (∃ e, e ∈ p.edges ∧ e ∈ q.edges) ∧ p.edges.toFinset ≠ q.edges.toFinset) :
    ¬ IsCactus G := by
  rintro ⟨-, hcac⟩
  obtain ⟨k, d, ⟨iso⟩⟩ := h
  obtain ⟨u, v, p, q, hp, hq, ⟨e, hep, heq⟩, hne⟩ := hw
  -- the composite embedding of the core into G
  set F : H →g G := (Hom.comp (iso.symm : pendantTower H k d ≃g G).toHom (towerHom H k d))
    with hF
  have hFinj : Function.Injective F := by
    intro a b hab
    exact towerHom_injective k d (iso.symm.toEquiv.injective hab)
  have hp' : (p.map F).IsCycle := (Walk.isCycle_map_iff_of_injective hFinj).mpr hp
  have hq' : (q.map F).IsCycle := (Walk.isCycle_map_iff_of_injective hFinj).mpr hq
  have hshared : Sym2.map F e ∈ (p.map F).edges := by
    rw [Walk.edges_map]
    exact List.mem_map_of_mem hep
  have hshared' : Sym2.map F e ∈ (q.map F).edges := by
    rw [Walk.edges_map]
    exact List.mem_map_of_mem heq
  have heqsets := hcac (p.map F) (q.map F) hp' hq' (Sym2.map F e) hshared hshared'
  rw [edges_toFinset_map, edges_toFinset_map] at heqsets
  exact hne (Finset.image_injective (Sym2.map.injective hFinj) heqsets)

end CactusExclusion

section ConcreteCores

/-- The one-vertex graph has no cycles at all, hence at most one. -/
theorem hasAtMostOneCycle_pathG_zero : HasAtMostOneCycle (pathG 0) := by
  intro u v p q hp hq
  exfalso
  have : ∀ x y : PathV 0, ¬ (pathG 0).Adj x y := by decide
  cases p with
  | nil => exact hp.not_nil Walk.nil_nil
  | cons hadj _ => exact this _ _ hadj

end ConcreteCores

section ThetaWitness

/-- Named vertices of `θ₁ = K₂,₃`: the two degree-3 hubs are `s` and `t` (the path ends); the
three degree-2 vertices are the path middle, the inner apex, and the outer apex. -/
private abbrev θs : ThetaV 1 := some (some (pathStart 2))
private abbrev θmid : ThetaV 1 := some (some (some none))
private abbrev θt : ThetaV 1 := some (some (pathEnd 2))
private abbrev θa : ThetaV 1 := some none
private abbrev θb : ThetaV 1 := none

/-- The 4-cycle through the path middle and the inner apex. -/
private def θcyc1 : (theta 1).Walk θs θs :=
  Walk.cons (show (theta 1).Adj θs θmid by decide)
    (Walk.cons (show (theta 1).Adj θmid θt by decide)
      (Walk.cons (show (theta 1).Adj θt θa by decide)
        (Walk.cons (show (theta 1).Adj θa θs by decide) Walk.nil)))

/-- The 4-cycle through the path middle and the outer apex. -/
private def θcyc2 : (theta 1).Walk θs θs :=
  Walk.cons (show (theta 1).Adj θs θmid by decide)
    (Walk.cons (show (theta 1).Adj θmid θt by decide)
      (Walk.cons (show (theta 1).Adj θt θb by decide)
        (Walk.cons (show (theta 1).Adj θb θs by decide) Walk.nil)))

private theorem θcyc1_isCycle : θcyc1.IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · decide
  · simp [θcyc1]
  · decide

private theorem θcyc2_isCycle : θcyc2.IsCycle := by
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · decide
  · simp [θcyc2]
  · decide

/-- **`θ₁ = K₂,₃` has two cycles sharing an edge with different edge sets.** -/
theorem theta_one_two_cycles :
    ∃ (u v : ThetaV 1) (p : (theta 1).Walk u u) (q : (theta 1).Walk v v),
      p.IsCycle ∧ q.IsCycle ∧
      (∃ e, e ∈ p.edges ∧ e ∈ q.edges) ∧ p.edges.toFinset ≠ q.edges.toFinset :=
  ⟨θs, θs, θcyc1, θcyc2, θcyc1_isCycle, θcyc2_isCycle,
    ⟨s(θs, θmid), by decide, by decide⟩, by decide⟩

end ThetaWitness

section K23Exclusion

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **A cactus never has core `K₂,₃`** (handoff §3): each edge of `K₂,₃` lies on two cycles. -/
theorem not_isCactus_of_coreIsK23 (h : CoreIsK23 G) : ¬ IsCactus G :=
  not_isCactus_of_coreIs_witness h theta_one_two_cycles

end K23Exclusion

section CycleIncidence

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- **Every vertex on a cycle carries two distinct cycle edges.** Rotate the cycle to start at
the vertex; the first and last darts give the two edges. -/
theorem exists_two_incident_edges_of_isCycle {u₀ : V} {c : G.Walk u₀ u₀} (hc : c.IsCycle)
    {u : V} (hu : u ∈ c.support) :
    ∃ v w, v ≠ w ∧ G.Adj u v ∧ G.Adj u w ∧
      s(u, v) ∈ c.edges ∧ s(u, w) ∈ c.edges := by
  have hcyc : (c.rotate u hu).IsCycle := hc.rotate hu
  have hnil : ¬ (c.rotate u hu).Nil := hcyc.not_nil
  have hmem : ∀ e, e ∈ (c.rotate u hu).edges → e ∈ c.edges := fun e he =>
    (c.rotate_edges u hu).perm.mem_iff.mp he
  refine ⟨(c.rotate u hu).snd, (c.rotate u hu).penultimate,
    hcyc.snd_ne_penultimate, (c.rotate u hu).adj_snd hnil,
    ((c.rotate u hu).adj_penultimate hnil).symm, ?_, ?_⟩
  · apply hmem
    have h1 := (c.rotate u hu).edge_firstDart hnil
    have h2 : ((c.rotate u hu).firstDart hnil) ∈ (c.rotate u hu).darts :=
      Walk.firstDart_mem_darts hnil
    rw [← h1]
    exact List.mem_map_of_mem h2
  · apply hmem
    have h1 := (c.rotate u hu).edge_lastDart hnil
    have h2 : ((c.rotate u hu).lastDart hnil) ∈ (c.rotate u hu).darts :=
      Walk.lastDart_mem_darts hnil
    have h3 : s((c.rotate u hu).penultimate, u) ∈ (c.rotate u hu).edges := by
      rw [← h1]
      exact List.mem_map_of_mem h2
    rw [Sym2.eq_swap] at h3
    exact h3

/-- No cycles exist in a graph on fewer than three vertices. -/
theorem not_isCycle_of_card_lt_three [Fintype V] (h : Fintype.card V < 3) {u : V}
    {c : G.Walk u u} : ¬ c.IsCycle := by
  intro hc
  have h3 := hc.three_le_length
  have hlen : c.support.tail.length = c.length := by
    have := c.length_support
    simp [List.length_tail, this]
  have hle : c.support.tail.length ≤ Fintype.card V :=
    List.Nodup.length_le_card hc.support_nodup
  omega

end CycleIncidence

section PathNeighbors

/-- The last-attached endpoint of a path has at most one neighbour. -/
theorem pathG_end_unique : ∀ (k : ℕ) {x y : PathV k},
    (pathG k).Adj (pathEnd k) x → (pathG k).Adj (pathEnd k) y → x = y
  | 0, x, y, hx, _ => absurd hx (by simp [pathG_zero])
  | k + 1, x, y, hx, hy => by
      match x, hx with
      | some b, hx =>
        match y, hy with
        | some c, hy =>
          have hb : b = pathEnd k := hx
          have hc : c = pathEnd k := hy
          rw [hb, hc]

/-- The first endpoint of a path has at most one neighbour. -/
theorem pathG_start_unique : ∀ (k : ℕ) {x y : PathV k},
    (pathG k).Adj (pathStart k) x → (pathG k).Adj (pathStart k) y → x = y
  | 0, x, y, hx, _ => absurd hx (by simp [pathG_zero])
  | 1, x, y, hx, hy => by revert hx hy; revert x y; decide
  | k + 2, x, y, hx, hy => by
      match x, hx with
      | none, hx =>
        exact absurd (show pathStart (k + 1) = pathEnd (k + 1) from hx)
          (by simp [pathStart, pathEnd])
      | some b, hx =>
        match y, hy with
        | none, hy =>
          exact absurd (show pathStart (k + 1) = pathEnd (k + 1) from hy)
            (by simp [pathStart, pathEnd])
        | some c, hy =>
          exact congrArg some (pathG_start_unique (k + 1) hx hy)

/-- **Paths have no vertex with three distinct neighbours.** -/
theorem pathG_no_three_nbrs : ∀ (k : ℕ) {u v w x : PathV k},
    (pathG k).Adj u v → (pathG k).Adj u w → (pathG k).Adj u x →
    v = w ∨ v = x ∨ w = x
  | 0, u, v, w, x, hv, _, _ => absurd hv (by simp [pathG_zero])
  | k + 1, u, v, w, x, hv, hw, hx => by
      match u with
      | none =>
        exact Or.inl (pathG_end_unique (k + 1) hv hw)
      | some a =>
        match v, hv with
        | none, hv =>
          match w, hw with
          | none, _ => exact Or.inl rfl
          | some b, hw =>
            match x, hx with
            | none, _ => exact Or.inr (Or.inl rfl)
            | some c, hx =>
              -- a = pathEnd k, and b, c are pathG k neighbours of the end: unique
              have ha : a = pathEnd k := hv
              subst ha
              exact Or.inr (Or.inr (congrArg some (pathG_end_unique k hw hx)))
        | some b, hv =>
          match w, hw with
          | none, hw =>
            match x, hx with
            | none, _ => exact Or.inr (Or.inr rfl)
            | some c, hx =>
              have ha : a = pathEnd k := hw
              subst ha
              exact Or.inr (Or.inl (congrArg some (pathG_end_unique k hv hx)))
          | some c, hw =>
            match x, hx with
            | none, hx =>
              have ha : a = pathEnd k := hx
              subst ha
              exact Or.inl (congrArg some (pathG_end_unique k hv hw))
            | some d, hx =>
              rcases pathG_no_three_nbrs k hv hw hx with h | h | h
              · exact Or.inl (congrArg some h)
              · exact Or.inr (Or.inl (congrArg some h))
              · exact Or.inr (Or.inr (congrArg some h))

end PathNeighbors

section ClosePathRigidity

/-- **The closed path has no vertex with three distinct neighbours.** -/
theorem closePath_no_three_nbrs : ∀ (k : ℕ) {u v w x : PathV (k + 1)},
    (closePath (k + 1)).Adj u v → (closePath (k + 1)).Adj u w → (closePath (k + 1)).Adj u x →
    v = w ∨ v = x ∨ w = x := by
  intro k u v w x hv hw hx
  match u with
  | none =>
    -- neighbours of the closing vertex are among `some (pathEnd k)`, `some (pathStart k)`
    match v, hv with
    | some b, hv =>
      match w, hw with
      | some c, hw =>
        match x, hx with
        | some d, hx =>
          rcases (hv : b = pathEnd k ∨ b = pathStart k) with hb | hb <;>
            rcases (hw : c = pathEnd k ∨ c = pathStart k) with hc | hc <;>
              rcases (hx : d = pathEnd k ∨ d = pathStart k) with hd | hd
          · exact Or.inl (congrArg some (hb.trans hc.symm))
          · exact Or.inl (congrArg some (hb.trans hc.symm))
          · exact Or.inr (Or.inl (congrArg some (hb.trans hd.symm)))
          · exact Or.inr (Or.inr (congrArg some (hc.trans hd.symm)))
          · exact Or.inr (Or.inr (congrArg some (hc.trans hd.symm)))
          · exact Or.inr (Or.inl (congrArg some (hb.trans hd.symm)))
          · exact Or.inl (congrArg some (hb.trans hc.symm))
          · exact Or.inl (congrArg some (hb.trans hc.symm))
  | some a =>
    match v, hv with
    | none, hv =>
      match w, hw with
      | none, _ => exact Or.inl rfl
      | some c, hw =>
        match x, hx with
        | none, _ => exact Or.inr (Or.inl rfl)
        | some d, hx =>
          rcases (hv : a = pathEnd k ∨ a = pathStart k) with ha | ha
          · subst ha
            exact Or.inr (Or.inr (congrArg some (pathG_end_unique k hw hx)))
          · subst ha
            exact Or.inr (Or.inr (congrArg some (pathG_start_unique k hw hx)))
    | some b, hv =>
      match w, hw with
      | none, hw =>
        match x, hx with
        | none, _ => exact Or.inr (Or.inr rfl)
        | some d, hx =>
          rcases (hw : a = pathEnd k ∨ a = pathStart k) with ha | ha
          · subst ha
            exact Or.inr (Or.inl (congrArg some (pathG_end_unique k hv hx)))
          · subst ha
            exact Or.inr (Or.inl (congrArg some (pathG_start_unique k hv hx)))
      | some c, hw =>
        match x, hx with
        | none, hx =>
          rcases (hx : a = pathEnd k ∨ a = pathStart k) with ha | ha
          · subst ha
            exact Or.inl (congrArg some (pathG_end_unique k hv hw))
          · subst ha
            exact Or.inl (congrArg some (pathG_start_unique k hv hw))
        | some d, hx =>
          rcases pathG_no_three_nbrs k hv hw hx with h | h | h
          · exact Or.inl (congrArg some h)
          · exact Or.inr (Or.inl (congrArg some h))
          · exact Or.inr (Or.inr (congrArg some h))

/-- Every vertex of a path reaches the last-attached end. -/
theorem pathG_reachable_end : ∀ (k : ℕ) (a : PathV k),
    Nonempty ((pathG k).Walk a (pathEnd k))
  | 0, _ => ⟨Walk.nil⟩
  | k + 1, none => ⟨Walk.nil⟩
  | k + 1, some b => by
      obtain ⟨p⟩ := pathG_reachable_end k b
      have hadj : (pathG (k + 1)).Adj (some (pathEnd k)) none := by
        show (pathG k).addPendantAdj (pathEnd k) (some (pathEnd k)) none
        simp [SimpleGraph.addPendantAdj]
      exact ⟨(p.map (somePendantHom (pathG k) (pathEnd k))).concat hadj⟩

theorem pathG_connected (k : ℕ) : (pathG k).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨pathEnd k⟩⟩
  obtain ⟨p⟩ := pathG_reachable_end k a
  obtain ⟨q⟩ := pathG_reachable_end k b
  exact ⟨p.append q.reverse⟩

theorem closePath_connected (k : ℕ) : (closePath (k + 1)).Connected :=
  (pathG_connected (k + 1)).mono (pathG_le_closePath (k + 1))

/-- **Cycle rigidity for the closed path**: any two cycles have the same edge set, i.e. the
closed path has at most one cycle. -/
theorem hasAtMostOneCycle_closePath : ∀ (k : ℕ), HasAtMostOneCycle (closePath k)
  | 0 => by
      intro u v p q hp _
      exact absurd hp (not_isCycle_of_card_lt_three (by decide))
  | 1 => by
      intro u v p q hp _
      exact absurd hp (not_isCycle_of_card_lt_three (by decide))
  | k + 2 => by
      -- every cycle is edge-closed at each visited vertex, and visits everything
      have hclosed : ∀ {u₀ : PathV (k + 2)} {c : (closePath (k + 2)).Walk u₀ u₀},
          c.IsCycle → ∀ u ∈ c.support, ∀ x, (closePath (k + 2)).Adj u x →
            s(u, x) ∈ c.edges := by
        intro u₀ c hc u hu x hx
        obtain ⟨v, w, hvw, hv, hw, hev, hew⟩ := exists_two_incident_edges_of_isCycle hc hu
        rcases closePath_no_three_nbrs (k + 1) hx hv hw with h | h | h
        · rw [h]; exact hev
        · rw [h]; exact hew
        · exact absurd h hvw
      have hvisit : ∀ {u₀ : PathV (k + 2)} {c : (closePath (k + 2)).Walk u₀ u₀},
          c.IsCycle → ∀ z, z ∈ c.support := by
        intro u₀ c hc z
        obtain ⟨W⟩ := (closePath_connected (k + 1)).preconnected u₀ z
        have step : ∀ {a b : PathV (k + 2)} (W : (closePath (k + 2)).Walk a b),
            a ∈ c.support → b ∈ c.support := by
          intro a b W
          induction W with
          | nil => exact id
          | cons hadj p ih =>
            intro ha
            exact ih (c.snd_mem_support_of_mem_edges (hclosed hc _ ha _ hadj))
        exact step W c.start_mem_support
      intro u v p q hp hq
      ext e
      simp only [List.mem_toFinset]
      induction e with
      | _ a b =>
        constructor
        · intro he
          exact hclosed hq a (hvisit hq a) b (p.adj_of_mem_edges he)
        · intro he
          exact hclosed hp a (hvisit hp a) b (q.adj_of_mem_edges he)

end ClosePathRigidity

section ForwardDirection

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The forward `k = 2` direction for cacti**: a `2`-ECC connected cactus has at most one
cycle or an odd cycle. The four core alternatives of the formalized Kirov–Naimi Theorem 2
(`ListColoring.ecc_two_iff`) map to the two disjuncts; the `K₂,₃` alternative is impossible
for a cactus. -/
theorem hasAtMostOneCycle_or_hasOddCycle_of_ecc_two (hG : IsCactus G) (h2 : G.ECCAt 2) :
    HasAtMostOneCycle G ∨ HasOddCycle G := by
  rcases (ecc_two_iff G hG.1).mp h2 with h | h | h | h
  · exact Or.inl (hasAtMostOneCycle_of_coreIs h hasAtMostOneCycle_pathG_zero)
  · obtain ⟨k, _, hcore⟩ := h
    exact Or.inl (hasAtMostOneCycle_of_coreIs hcore (hasAtMostOneCycle_closePath k))
  · exact absurd hG (not_isCactus_of_coreIsK23 h)
  · exact Or.inr h

end ForwardDirection

end ListColoring
