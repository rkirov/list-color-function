/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.CoreExtract
import ListColoring.RubinCases
import ListColoring.Theorem2

/-!
# Rubin's theorem, and Theorem 2 of Kirov–Naimi unconditionally

**Rubin's theorem.** *A connected graph is `2`-choosable iff its core is a single vertex, an even
cycle, or `θ_{2,2,2m}` for some `m ≥ 1`.*

Due to **A. L. Rubin**, and published in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in
graphs*, Proc. West Coast Conf. on Combinatorics, Graph Theory and Computing (Arcata, California,
1979), Congr. Numer. **26**, Utilitas Math., Winnipeg, **1980**, 125–157, pp. 131–134. **Nothing in
this file is new mathematics.** It is a 1980 theorem; what is new is only that a machine has now
checked it.

This file is the last step: every ingredient was already proved, and here they are put together.

* `ListColoring.hasCore` (`ListColoring/CoreExtract.lean`) produces the core `H` of a connected `G`,
  which is connected and either a single vertex or of minimum degree at least `2`;
* `ListColoring.choosable_iff_of_coreIs` (`ListColoring/Theorem2.lean`) says `G` is `2`-choosable
  exactly when `H` is;
* `ListColoring.rubin_structure` (`ListColoring/RubinCases.lean`) — Rubin's steps 1–6 — says that a
  connected, `2`-choosable `H` of minimum degree at least `2` carries either a spanning cycle of
  even length or a labelled `θ_{2,2,2m}`, stated as data about walks;
* `ListColoring.exists_iso_closePath_of_two_regular` and
  `ListColoring.nonempty_iso_thetaGen_of_paths` (`ListColoring/CoreExtract.lean`) turn that walk
  data into isomorphisms;
* `ListColoring.choosable_two_of_rubinAlternatives` (`ListColoring/Theorem2.lean`) is the ⟸
  direction.

What is genuinely proved here, rather than merely quoted, is the glue: transporting
`ListColoring.CoreIs` along an isomorphism of the core, the counting argument that a graph of
minimum degree `≥ 2` whose edges all lie on one cycle is `2`-regular, and the bookkeeping that
presents the four-cycle-plus-path of the theta case as three internally disjoint arms.

Because `ListColoring/Theorem2.lean` is *upstream* of `ListColoring/CoreExtract.lean` and
`ListColoring/RubinCases.lean` — `ListColoring.HasCore` is stated in terms of `ListColoring.CoreIs`
— the unconditional form of Kirov–Naimi's Theorem 2 has to be stated here rather than there;
`ListColoring.ecc_two_iff_of_rubin` is applied to `ListColoring.rubinTheorem` with no other change.

## Main results

* `ListColoring.CoreIs.congr` : `ListColoring.CoreIs` only sees the core up to isomorphism
* `ListColoring.degree_eq_two_of_cycle_edges` : minimum degree `≥ 2` plus "every edge lies on the
  cycle `c`" forces `2`-regularity
* `ListColoring.exists_iso_theta_of_thetaData` : the theta case of Rubin's structure theorem, as an
  isomorphism onto `ListColoring.theta m`
* `ListColoring.rubinTheorem` : **Rubin's theorem**
* `ListColoring.ecc_two_iff` : **Theorem 2 of Kirov–Naimi, unconditionally**
-/

open Finset SimpleGraph

namespace ListColoring

/-! ### Transporting `CoreIs` along an isomorphism of the core -/

/-- A tower of pendant attachments can be transported along an isomorphism of the base graph. -/
theorem exists_pendantTower_iso {W W' : Type} [Fintype W] [DecidableEq W] [Fintype W']
    [DecidableEq W'] {H : SimpleGraph W} [DecidableRel H.Adj] {H' : SimpleGraph W'}
    [DecidableRel H'.Adj] (e : H ≃g H') :
    ∀ (k : ℕ) (d : TowerData W k), ∃ d' : TowerData W' k,
      Nonempty (pendantTower H k d ≃g pendantTower H' k d') := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨PUnit.unit, ⟨e⟩⟩
  | succ k ih =>
      intro d
      obtain ⟨d', ⟨f⟩⟩ := ih d.1
      exact ⟨(d', f d.2), ⟨addPendantIso f d.2⟩⟩

/-- **`CoreIs` only sees the core up to isomorphism.** -/
theorem CoreIs.congr {V W W' : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype W'] [DecidableEq W'] {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    [DecidableRel H.Adj] {H' : SimpleGraph W'} [DecidableRel H'.Adj]
    (h : CoreIs G H) (e : H ≃g H') : CoreIs G H' := by
  obtain ⟨k, d, ⟨g⟩⟩ := h
  obtain ⟨d', ⟨f⟩⟩ := exists_pendantTower_iso e k d
  exact ⟨k, d', ⟨g.trans f⟩⟩

/-- A graph with exactly one vertex is `ListColoring.pathG 0`. -/
theorem nonempty_iso_pathG_zero {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hcard : Fintype.card W = 1) : Nonempty (H ≃g pathG 0) := by
  haveI : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
  have hcard' : Fintype.card W = Fintype.card (PathV 0) := by rw [hcard]; rfl
  refine ⟨⟨Fintype.equivOfCardEq hcard', ?_⟩⟩
  intro a b
  refine ⟨fun h => h.elim, fun h => absurd h ?_⟩
  rw [Subsingleton.elim a b]
  exact H.irrefl

/-! ### Small walk lemmas -/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every edge of a walk is a step of it: the converse of `ListColoring.getVert_mem_edges`. -/
theorem exists_getVert_of_mem_edges {x y : V} (p : G.Walk x y) : ∀ {e : Sym2 V}, e ∈ p.edges →
    ∃ i, i < p.length ∧ e = s(p.getVert i, p.getVert (i + 1)) := by
  induction p with
  | nil => intro e he; simp at he
  | @cons u v w h q ih =>
      intro e he
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨i, hi, hie⟩ := ih he
        refine ⟨i + 1, by simp only [SimpleGraph.Walk.length_cons]; omega, ?_⟩
        simpa using hie

/-- A triangle forbids a `2`-coloring, hence a `2`-list-coloring. -/
theorem false_of_triangle_of_choosable_two {x y z : V} (hch : G.Choosable 2)
    (h1 : G.Adj x y) (h2 : G.Adj y z) (h3 : G.Adj z x) : False := by
  obtain ⟨col⟩ := colorable_of_choosable hch
  have e1 := col.valid h1
  have e2 := col.valid h2
  have e3 := col.valid h3
  revert e1 e2 e3
  generalize col x = A
  generalize col y = B
  generalize col z = C
  revert A B C
  decide

/-! ### The even-cycle branch -/

/-- **A graph of minimum degree `≥ 2` all of whose edges lie on one cycle is `2`-regular.**

Counting: the cycle has `c.length` distinct vertices, so `c.length ≤ |V|`; every edge is one of the
`c.length` edges of the cycle, so `|E| ≤ c.length`; and the degree-sum formula turns
`2|V| ≤ ∑ deg = 2|E| ≤ 2 c.length ≤ 2|V|` into an equality, which with `deg ≥ 2` everywhere forces
`deg = 2` everywhere. -/
theorem degree_eq_two_of_cycle_edges {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {v : W} {c : H.Walk v v} (hc : c.IsCycle)
    (hdeg : ∀ z : W, 2 ≤ H.degree z) (hall : ∀ x y : W, H.Adj x y → s(x, y) ∈ c.edges) :
    ∀ z : W, H.degree z = 2 := by
  classical
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]; omega
  have hcardV : c.length ≤ Fintype.card W := by
    have h1 : c.support.tail.toFinset.card = c.length := by
      rw [List.toFinset_card_of_nodup hc.support_nodup, hlen]
    have h2 := Finset.card_le_univ c.support.tail.toFinset
    rw [h1] at h2
    simpa using h2
  have hE : H.edgeFinset.card ≤ c.length := by
    have hsub : H.edgeFinset ⊆ c.edges.toFinset := by
      intro e
      induction e using Sym2.ind with
      | _ x y =>
          intro he
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          exact List.mem_toFinset.mpr (hall x y he)
    calc H.edgeFinset.card ≤ c.edges.toFinset.card := Finset.card_le_card hsub
      _ ≤ c.edges.length := List.toFinset_card_le _
      _ = c.length := c.length_edges
  have hsum : ∑ z, H.degree z = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  intro z
  by_contra hne
  have hlt : ∑ _x : W, 2 < ∑ x, H.degree x :=
    Finset.sum_lt_sum (fun i _ => hdeg i) ⟨z, Finset.mem_univ z, by have := hdeg z; omega⟩
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
  omega

/-! ### The theta branch -/

/-- The arm `s → m → t` of length two, as a function of the index. -/
def twoArm {W : Type} (s m t : W) : ℕ → W :=
  fun i => if i = 0 then s else if i = 1 then m else t

@[simp] lemma twoArm_zero {W : Type} (s m t : W) : twoArm s m t 0 = s := rfl

@[simp] lemma twoArm_one {W : Type} (s m t : W) : twoArm s m t 1 = m := rfl

@[simp] lemma twoArm_two {W : Type} (s m t : W) : twoArm s m t 2 = t := rfl

/-- The four named vertices of a four-cycle whose support they exhaust really lie on it: the cycle
has four distinct vertices and they are drawn from a set of at most four. -/
theorem mem_support_of_cycle_four {W : Type} [DecidableEq W] {H : SimpleGraph W} {z : W}
    {c : H.Walk z z} (hc : c.IsCycle) (hlen4 : c.length = 4) {a u b w : W}
    (hcsup : ∀ x, x ∈ c.support → x = a ∨ x = u ∨ x = b ∨ x = w) :
    u ∈ c.support ∧ w ∈ c.support := by
  classical
  have hlen : c.support.tail.length = 4 := by
    rw [List.length_tail, SimpleGraph.Walk.length_support, hlen4]
  have hcard : c.support.tail.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hc.support_nodup, hlen]
  have hsub : c.support.tail.toFinset ⊆ ([a, u, b, w] : List W).toFinset := by
    intro x hx
    have hx' : x ∈ c.support := List.tail_subset _ (List.mem_toFinset.mp hx)
    rcases hcsup x hx' with rfl | rfl | rfl | rfl <;> simp
  have hle : ([a, u, b, w] : List W).toFinset.card ≤ c.support.tail.toFinset.card := by
    have := List.toFinset_card_le ([a, u, b, w] : List W)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have heq : c.support.tail.toFinset = ([a, u, b, w] : List W).toFinset :=
    Finset.eq_of_subset_of_card_le hsub hle
  have key : ∀ x : W, x ∈ ([a, u, b, w] : List W) → x ∈ c.support := by
    intro x hx
    have hx' : x ∈ c.support.tail.toFinset := by rw [heq]; exact List.mem_toFinset.mpr hx
    exact List.tail_subset _ (List.mem_toFinset.mp hx')
  exact ⟨key u (by simp), key w (by simp)⟩

/-- **The theta case of Rubin's structure theorem, as an isomorphism.** The labelled walk data
produced by `ListColoring.rubin_structure` — a four-cycle `a, u, b, w` together with an even path
`p` from `a` to `b` internally disjoint from it, the two exhausting the vertices and edges of `H` —
presents `H` as three internally disjoint paths from `a` to `b` of lengths `2`, `2` and `p.length`,
hence as `θ_{2,2,2m}`.

Due to **A. L. Rubin**, in Erdős–Rubin–Taylor, *Choosability in graphs*, Congr. Numer. **26**
(1980), 125–157, pp. 131–134, who writes "`C₁ ∪ P₁ = θ_{2,2,2m}`" and passes on. Not novel. -/
theorem exists_iso_theta_of_thetaData {W : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (hch : H.Choosable 2) {z : W} {c : H.Walk z z} {a b u w : W}
    {p : H.Walk a b} (hc : c.IsCycle) (hlen4 : c.length = 4) (hab : a ≠ b) (huw : u ≠ w)
    (hau : H.Adj a u) (hub : H.Adj u b) (haw : H.Adj a w) (hwb : H.Adj w b)
    (hcsup : ∀ x, x ∈ c.support → x = a ∨ x = u ∨ x = b ∨ x = w)
    (hp : p.IsPath) (hev : Even p.length) (hl2 : 2 ≤ p.length)
    (hpint : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support)
    (hzcov : ∀ x : W, x ∈ c.support ∨ x ∈ p.support)
    (hall : ∀ x y : W, H.Adj x y → s(x, y) ∈ c.edges ∨ s(x, y) ∈ p.edges) :
    ∃ m, 1 ≤ m ∧ Nonempty (H ≃g theta m) := by
  classical
  obtain ⟨husup, hwsup⟩ := mem_support_of_cycle_four hc hlen4 hcsup
  obtain ⟨m, hm⟩ : ∃ m, p.length = 2 * m := by obtain ⟨t, ht⟩ := hev; exact ⟨t, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hune : u ≠ a := hau.ne'
  have hunb : u ≠ b := hub.ne
  have hwna : w ≠ a := haw.ne'
  have hwnb : w ≠ b := hwb.ne
  have hrin : ∀ i, 0 < i → i < p.length → p.getVert i ≠ a ∧ p.getVert i ≠ b := by
    intro i hi0 hil
    constructor
    · intro h
      have : i = 0 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) (h.trans p.getVert_zero.symm)
      omega
    · intro h
      have : i = p.length := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) (h.trans p.getVert_length.symm)
      omega
  have hrout : ∀ i, 0 < i → i < p.length → p.getVert i ∉ c.support := fun i hi0 hil =>
    hpint _ (p.getVert_mem_support i) (hrin i hi0 hil).1 (hrin i hi0 hil).2
  have hiso : Nonempty (H ≃g thetaGen 2 2 p.length) := by
    refine nonempty_iso_thetaGen_of_paths (a := 2) (b := 2) (c := p.length) (x := a) (y := b)
      (p := twoArm a u b) (q := twoArm a w b) (r := p.getVert)
      one_le_two one_le_two (by omega) hab
      (twoArm_zero a u b) (twoArm_two a u b) (twoArm_zero a w b) (twoArm_two a w b)
      p.getVert_zero p.getVert_length
      ?hpadj ?hqadj ?hradj ?hpin ?hqin ?hrin ?hpinj ?hqinj ?hrinj ?hpq ?hpr ?hqr ?hcov ?hedg
    case hpadj =>
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · simpa using hau
      · simpa using hub
    case hqadj =>
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · simpa using haw
      · simpa using hwb
    case hradj => intro i hi; exact p.adj_getVert_succ hi
    case hpin =>
      intro i hi0 hi2
      obtain rfl : i = 1 := by omega
      simpa using ⟨hune, hunb⟩
    case hqin =>
      intro i hi0 hi2
      obtain rfl : i = 1 := by omega
      simpa using ⟨hwna, hwnb⟩
    case hrin => exact hrin
    case hpinj => intro i hi0 hi2 j hj0 hj2 _; omega
    case hqinj => intro i hi0 hi2 j hj0 hj2 _; omega
    case hrinj =>
      intro i hi0 hi2 j hj0 hj2 he
      exact hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) he
    case hpq =>
      intro i hi0 hi2 j hj0 hj2
      obtain rfl : i = 1 := by omega
      obtain rfl : j = 1 := by omega
      simpa using huw
    case hpr =>
      intro i hi0 hi2 j hj0 hjl
      obtain rfl : i = 1 := by omega
      simp only [twoArm_one]
      intro he
      exact hrout j hj0 hjl (he ▸ husup)
    case hqr =>
      intro i hi0 hi2 j hj0 hjl
      obtain rfl : i = 1 := by omega
      simp only [twoArm_one]
      intro he
      exact hrout j hj0 hjl (he ▸ hwsup)
    case hcov =>
      intro x
      rcases hzcov x with hx | hx
      · rcases hcsup x hx with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨0, by omega, rfl⟩
        · exact Or.inl ⟨1, by omega, rfl⟩
        · exact Or.inl ⟨2, by omega, rfl⟩
        · exact Or.inr (Or.inl ⟨1, by omega, rfl⟩)
      · obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
        exact Or.inr (Or.inr ⟨n, hnle, hn⟩)
    case hedg =>
      intro x y hxy
      rcases hall x y hxy with he | he
      · have hx := hcsup x (c.fst_mem_support_of_mem_edges he)
        have hy := hcsup y (c.snd_mem_support_of_mem_edges he)
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
        · exact absurd hxy H.irrefl
        · exact Or.inl ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩
        · exact (false_of_triangle_of_choosable_two hch hau hub hxy.symm).elim
        · exact Or.inr (Or.inl ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩)
        · exact Or.inl ⟨0, by omega, Or.inr ⟨rfl, rfl⟩⟩
        · exact absurd hxy H.irrefl
        · exact Or.inl ⟨1, by omega, Or.inl ⟨rfl, rfl⟩⟩
        · exact (false_of_triangle_of_choosable_two hch hau hxy haw.symm).elim
        · exact (false_of_triangle_of_choosable_two hch hxy hau hub).elim
        · exact Or.inl ⟨1, by omega, Or.inr ⟨rfl, rfl⟩⟩
        · exact absurd hxy H.irrefl
        · exact Or.inr (Or.inl ⟨1, by omega, Or.inr ⟨rfl, rfl⟩⟩)
        · exact Or.inr (Or.inl ⟨0, by omega, Or.inr ⟨rfl, rfl⟩⟩)
        · exact (false_of_triangle_of_choosable_two hch hau hxy.symm haw.symm).elim
        · exact Or.inr (Or.inl ⟨1, by omega, Or.inl ⟨rfl, rfl⟩⟩)
        · exact absurd hxy H.irrefl
      · obtain ⟨i, hi, hie⟩ := exists_getVert_of_mem_edges p he
        refine Or.inr (Or.inr ⟨i, hi, ?_⟩)
        rw [Sym2.eq_iff] at hie
        rcases hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
  rw [hm] at hiso
  exact ⟨m, hm1, nonempty_iso_theta_of_iso_thetaGen hm1 hiso⟩

/-! ### Rubin's theorem -/

/-- **Rubin's theorem.**

> A connected graph is `2`-choosable iff its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

Due to **A. L. Rubin**, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc.
West Coast Conf. on Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congr.
Numer. **26**, Utilitas Math., Winnipeg, **1980**, 125–157, pp. 131–134. **Nothing here is new
mathematics**; this is Rubin's proof, mechanized.

The assembly. The ⟸ direction is `ListColoring.choosable_two_of_rubinAlternatives`. For ⟹, pass to
the core (`ListColoring.hasCore`), which is `2`-choosable because `G` is
(`ListColoring.choosable_iff_of_coreIs`). If the core is a single vertex we are in the first case.
Otherwise it has minimum degree at least `2`, so `ListColoring.rubin_structure` applies and returns
either a spanning cycle of even length — whence the core is `2`-regular
(`ListColoring.degree_eq_two_of_cycle_edges`) and so a cycle
(`ListColoring.exists_iso_closePath_of_two_regular`), necessarily an even one since an odd cycle is
not `2`-choosable — or a labelled `θ_{2,2,2m}` (`ListColoring.exists_iso_theta_of_thetaData`). -/
theorem rubinTheorem : RubinTheorem := by
  intro V _ _ G _ hconn
  refine ⟨fun hch => ?_, choosable_two_of_rubinAlternatives⟩
  obtain ⟨W, _, _, H, _, hHconn, hHcase, hcore⟩ := hasCore G hconn
  have hHch : H.Choosable 2 := (choosable_iff_of_coreIs hcore le_rfl).mp hch
  rcases hHcase with hcard1 | hdeg
  · exact Or.inl (hcore.congr (nonempty_iso_pathG_zero H hcard1).some)
  rcases rubin_structure hHconn hdeg hHch with
    ⟨_, c, hc, hev, _, hall⟩ |
    ⟨_, c, a, b, u, w, p, hc, hlen4, _, _, hab, huw, hau, hub, haw, hwb, hcsup, hp, hev,
      hl2, hpint, _, hzcov, hall⟩
  · refine Or.inr (Or.inl ?_)
    obtain ⟨k, hk2, ⟨e⟩⟩ :=
      exists_iso_closePath_of_two_regular hHconn (degree_eq_two_of_cycle_edges hc hdeg hall)
    refine ⟨k, ?_, hk2, hcore.congr e⟩
    rcases Nat.even_or_odd k with hk | hk
    · exact absurd ((choosable_iso e 2).mp hHch) (not_choosable_two_of_odd_cycle hk hk2)
    · exact hk
  · refine Or.inr (Or.inr ?_)
    obtain ⟨m, hm1, ⟨e⟩⟩ := exists_iso_theta_of_thetaData hHch hc hlen4 hab huw hau hub haw hwb
      hcsup hp hev hl2 hpint hzcov hall
    exact ⟨m, hm1, hcore.congr e⟩

/-! ### Theorem 2 of Kirov–Naimi, unconditionally -/

/-- **Theorem 2 of Kirov–Naimi, with no hypothesis beyond connectivity.**

> A connected graph is 2-monophilic iff its core is a single vertex, is a cycle, is `K₂,₃`, or
> contains an odd cycle.

That is the paper's wording; "2-monophilic" is `SimpleGraph.ECCAt G 2`, *enumeratively
chromatic-choosable at `2`*.

**Kirov–Naimi 2016**, *List coloring and `n`-monophilic graphs*, Ars Combin. **124** (2016),
329–340 (arXiv:1004.5183), Theorem 2. It appears again as Theorem 2(iv) of Chi, Lee, Morrissette,
Mudrock, Nguyen and Whatley (arXiv:2605.10861, 2026), there attributed to [1, 6, 13, 16, 17] with
Kirov–Naimi as [16]. The mathematics is theirs, and the one result they borrow — **Rubin's
theorem** — is now `ListColoring.rubinTheorem` rather than a hypothesis.

This is literally `ListColoring.ecc_two_iff_of_rubin` applied to `ListColoring.rubinTheorem`;
the proof of Theorem 2 itself is in `ListColoring/Theorem2.lean` and is unchanged. It has to be
stated in this file rather than there only because `ListColoring/Theorem2.lean` is upstream of the
files Rubin's theorem is proved from. -/
theorem ecc_two_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) :
    G.ECCAt 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G :=
  ecc_two_iff_of_rubin rubinTheorem G hconn

/-! ### Sanity checks

The parity and index conventions the assembly leans on, pinned down numerically. -/

section Guards

-- the two-step arm really is `s, m, t`
#guard [twoArm 7 8 9 0, twoArm 7 8 9 1, twoArm 7 8 9 2] = [7, 8, 9]

-- `closePath k` is the cycle on `k + 1` vertices, so `Odd k` is the *even* cycle: two proper
-- `2`-colorings, versus none for `Even k`
#guard [2, 3, 4, 5, 6, 7].all fun k => Fintype.card (PathV k) == k + 1
#guard [2, 3, 4, 5, 6, 7].all fun k => ((closePath k).colConst 2 == 2) == decide (Odd k)

-- `theta m` is `θ_{2,2,2m}`: a path on `2m + 1` vertices plus the two branch vertices, and
-- `2 + 2 + 2m` edges; `theta 1 = K₂,₃`
#guard [1, 2, 3].all fun m => Fintype.card (ThetaV m) == 2 * m + 3
#guard [1, 2, 3].all fun m => (theta m).edgeFinset.card == 2 * m + 4
#guard [1, 2, 3].all fun m => (theta m).edgeFinset.card == (thetaGen 2 2 (2 * m)).edgeFinset.card
#guard Fintype.card (ThetaV 1) = 5
#guard (theta 1).edgeFinset.card = 6

end Guards

end ListColoring

#print axioms ListColoring.exists_pendantTower_iso
#print axioms ListColoring.CoreIs.congr
#print axioms ListColoring.nonempty_iso_pathG_zero
#print axioms ListColoring.exists_getVert_of_mem_edges
#print axioms ListColoring.false_of_triangle_of_choosable_two
#print axioms ListColoring.degree_eq_two_of_cycle_edges
#print axioms ListColoring.mem_support_of_cycle_four
#print axioms ListColoring.exists_iso_theta_of_thetaData
#print axioms ListColoring.rubinTheorem
#print axioms ListColoring.ecc_two_iff
