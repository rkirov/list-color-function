/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.CycleGraph
import ListColoring.RubinProof
import ListColoring.Theorem2

/-!
# The classification on Mathlib's graphs

Restates Rubin's theorem and Kirov–Naimi's Theorem 2 with core alternatives written on Mathlib's
`SimpleGraph.cycleGraph`, on `⊥ : SimpleGraph (Fin 1)`, and on

* `SimpleGraph.thetaGraph m := (cycleGraph (2 * m + 2)).addPendantPair 0 2` —

`θ_{2,2,2m}` as the cycle `C_{2m+2}` plus one vertex joined to `0` and `2`.  With these the
statement surface (`comparator/Challenge.lean`) needs none of the development's path and cone
constructions.

The bridge: `CoreIs` and `Contains` respect isomorphism of the core (`coreIs_congr_right`,
`contains_congr_right`, via `exists_pendantTower_iso`), and the three concrete cores are
isomorphic to the development's models (`botFinOneIsoPathGZero`, `cycleGraphIsoClosePath`,
`thetaGraphIsoTheta`).
-/

namespace ListColoring

open SimpleGraph

/-- `CoreIs` respects isomorphism of the core, as an iff. -/
theorem coreIs_congr_right {V W W' : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype W'] [DecidableEq W'] {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    [DecidableRel H.Adj] {H' : SimpleGraph W'} [DecidableRel H'.Adj] (e : H ≃g H') :
    CoreIs G H ↔ CoreIs G H' :=
  ⟨fun h => h.congr e, fun h => h.congr e.symm⟩

/-- `Contains` respects isomorphism of the contained graph. -/
theorem contains_congr_right {V W W' : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    {K' : SimpleGraph W'} (e : K ≃g K') : Contains G K ↔ Contains G K' := by
  constructor
  · rintro ⟨f, hinj, hadj⟩
    exact ⟨f ∘ e.symm, hinj.comp e.symm.toEquiv.injective,
      fun a b hab => hadj _ _ (e.symm.map_rel_iff.mpr hab)⟩
  · rintro ⟨f, hinj, hadj⟩
    exact ⟨f ∘ e, hinj.comp e.toEquiv.injective,
      fun a b hab => hadj _ _ (e.map_rel_iff.mpr hab)⟩

/-- The one-vertex graph: Mathlib's `⊥` on `Fin 1` against the development's `pathG 0`. -/
def botFinOneIsoPathGZero : (⊥ : SimpleGraph (Fin 1)) ≃g pathG 0 where
  toEquiv :=
    { toFun := fun _ => pathVtx 0 0
      invFun := fun _ => 0
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun v => @Subsingleton.elim _ (inferInstanceAs (Subsingleton Unit)) _ _ }
  map_rel_iff' := by
    intro a b
    rw [pathG_zero]
    exact Iff.rfl

end ListColoring

namespace SimpleGraph

open ListColoring

/-- `θ_{2,2,2m}`, on Mathlib's cycle graph: the cycle `C_{2m+2}` together with one extra vertex
joined to `0` and `2`, which lie at distance two on the cycle.  The three arms between the branch
vertices `some 0` and `some 2` have lengths `2`, `2` and `2m`. -/
def thetaGraph (m : ℕ) : SimpleGraph (Option (Fin (2 * m + 2))) :=
  (cycleGraph (2 * m + 2)).addPendantPair 0 2

instance instDecidableRelThetaGraph (m : ℕ) : DecidableRel (thetaGraph m).Adj :=
  inferInstanceAs (DecidableRel ((cycleGraph (2 * m + 2)).addPendantPair 0 2).Adj)

/-- Adjacency in `cycleGraph (2 * m + 2)`, on values: cyclically consecutive. -/
private lemma cycleGraph_adj_val {m : ℕ} (a b : Fin (2 * m + 2)) :
    (cycleGraph (2 * m + 2)).Adj a b ↔
      (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨
        (a.val = 0 ∧ b.val = 2 * m + 1) ∨ (b.val = 0 ∧ a.val = 2 * m + 1)) := by
  have ha := a.isLt
  have hb := b.isLt
  have hsub : ∀ x y : Fin (2 * m + 2), (x - y).val = (2 * m + 2 - y.val + x.val) % (2 * m + 2) :=
    fun x y => by rw [Fin.sub_def]
  have hmod : ∀ t : ℕ, t < 2 * (2 * m + 2) →
      t % (2 * m + 2) = if t < 2 * m + 2 then t else t - (2 * m + 2) := by
    intro t ht
    by_cases h : t < 2 * m + 2
    · rw [if_pos h, Nat.mod_eq_of_lt h]
    · rw [if_neg h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [cycleGraph_adj', hsub a b, hsub b a, hmod _ (by omega), hmod _ (by omega)]
  split_ifs <;> omega

/-- The vertex relabelling behind `thetaGraphIsoTheta`: negate, then peel the last index off as
the inner cone vertex. -/
private def thetaEquivAux (m : ℕ) : Fin (2 * m + 2) ≃ Option (PathV (2 * m)) :=
  (Equiv.neg _).trans (finSuccEquivLast.trans (Equiv.optionCongr (pathVtxEquiv (2 * m))))

private lemma thetaEquivAux_apply (m : ℕ) (j : Fin (2 * m + 2)) :
    thetaEquivAux m j =
      if j.val = 1 then none
      else some (pathVtx (2 * m) (if j.val = 0 then 0 else 2 * m + 2 - j.val)) := by
  have hj := j.isLt
  have hval : (-j : Fin (2 * m + 2)).val = (2 * m + 2 - j.val) % (2 * m + 2) := by
    rw [Fin.neg_def]
  show Equiv.optionCongr (pathVtxEquiv (2 * m)) (finSuccEquivLast (-j)) = _
  by_cases h1 : j.val = 1
  · have hlast : (-j : Fin (2 * m + 2)) = Fin.last (2 * m + 1) := by
      apply Fin.ext
      rw [hval, h1, Nat.mod_eq_of_lt (by omega), Fin.val_last]
      omega
    rw [if_pos h1, hlast, finSuccEquivLast_last]
    rfl
  · have hsle : (if j.val = 0 then 0 else 2 * m + 2 - j.val) < 2 * m + 1 := by
      split_ifs <;> omega
    have hcast : (-j : Fin (2 * m + 2)) =
        Fin.castSucc ⟨if j.val = 0 then 0 else 2 * m + 2 - j.val, hsle⟩ := by
      apply Fin.ext
      rw [hval]
      show (2 * m + 2 - j.val) % (2 * m + 2) = if j.val = 0 then 0 else 2 * m + 2 - j.val
      by_cases h0 : j.val = 0
      · rw [if_pos h0, h0, Nat.sub_zero, Nat.mod_self]
      · rw [if_neg h0, Nat.mod_eq_of_lt (by omega)]
    rw [if_neg h1, hcast, finSuccEquivLast_castSucc]
    rfl

private lemma theta_adj_none_some_aux (m : ℕ) (hm : 1 ≤ m) (j : Fin (2 * m + 2)) :
    (theta m).Adj none (some (thetaEquivAux m j)) ↔ j = 0 ∨ j = 2 := by
  have hj := j.isLt
  have h0v : (0 : Fin (2 * m + 2)).val = 0 := rfl
  have h2v : (2 : Fin (2 * m + 2)).val = 2 := by
    have h : (2 : Fin (2 * m + 2)).val = 2 % (2 * m + 2) := rfl
    rw [h, Nat.mod_eq_of_lt (by omega)]
  rw [thetaEquivAux_apply,
    show (theta m) = coneOn (thetaBaseOf (2 * m))
      {some (pathStart (2 * m)), some (pathEnd (2 * m))} from rfl]
  by_cases h1 : j.val = 1
  · rw [if_pos h1, coneOn_adj_none_some]
    refine iff_of_false (by simp) ?_
    rintro (rfl | rfl)
    · rw [h0v] at h1; omega
    · rw [h2v] at h1; omega
  · rw [if_neg h1, coneOn_adj_none_some, Finset.mem_insert, Finset.mem_singleton,
      Option.some_inj, Option.some_inj,
      pathVtx_eq_pathStart_iff (by split_ifs <;> omega),
      pathVtx_eq_pathEnd_iff (by split_ifs <;> omega),
      show (j = 0) ↔ ((j : ℕ) = 0) from by rw [Fin.ext_iff, h0v],
      show (j = 2) ↔ ((j : ℕ) = 2) from by rw [Fin.ext_iff, h2v]]
    split_ifs <;> omega

private lemma theta_adj_some_some_aux (m : ℕ) (hm : 1 ≤ m) (j j' : Fin (2 * m + 2)) :
    (theta m).Adj (some (thetaEquivAux m j)) (some (thetaEquivAux m j')) ↔
      (cycleGraph (2 * m + 2)).Adj j j' := by
  have hj := j.isLt
  have hj' := j'.isLt
  rw [thetaEquivAux_apply, thetaEquivAux_apply, cycleGraph_adj_val,
    show (theta m) = coneOn (thetaBaseOf (2 * m))
      {some (pathStart (2 * m)), some (pathEnd (2 * m))} from rfl,
    coneOn_adj_some_some,
    show thetaBaseOf (2 * m) = coneOn (pathG (2 * m))
      {pathStart (2 * m), pathEnd (2 * m)} from rfl]
  by_cases h1 : j.val = 1 <;> by_cases h1' : j'.val = 1
  · rw [if_pos h1, if_pos h1']
    exact iff_of_false (coneOn_adj_none_none _ _) (by omega)
  · rw [if_pos h1, if_neg h1', coneOn_adj_none_some, Finset.mem_insert, Finset.mem_singleton,
      pathVtx_eq_pathStart_iff (by split_ifs <;> omega),
      pathVtx_eq_pathEnd_iff (by split_ifs <;> omega)]
    split_ifs <;> omega
  · rw [if_neg h1, if_pos h1', coneOn_adj_some_none, Finset.mem_insert, Finset.mem_singleton,
      pathVtx_eq_pathStart_iff (by split_ifs <;> omega),
      pathVtx_eq_pathEnd_iff (by split_ifs <;> omega)]
    split_ifs <;> omega
  · rw [if_neg h1, if_neg h1']
    by_cases h0 : (j : ℕ) = 0 <;> by_cases h0' : (j' : ℕ) = 0
    · rw [if_pos h0, if_pos h0', coneOn_adj_some_some,
        pathG_adj_pathVtx (2 * m) 0 0 (by omega) (by omega)]
      omega
    · rw [if_pos h0, if_neg h0', coneOn_adj_some_some,
        pathG_adj_pathVtx (2 * m) 0 (2 * m + 2 - (j' : ℕ)) (by omega) (by omega)]
      omega
    · rw [if_neg h0, if_pos h0', coneOn_adj_some_some,
        pathG_adj_pathVtx (2 * m) (2 * m + 2 - (j : ℕ)) 0 (by omega) (by omega)]
      omega
    · rw [if_neg h0, if_neg h0', coneOn_adj_some_some,
        pathG_adj_pathVtx (2 * m) (2 * m + 2 - (j : ℕ)) (2 * m + 2 - (j' : ℕ)) (by omega)
          (by omega)]
      omega

/-- `thetaGraph m` is the development's `theta m`. -/
def thetaGraphIsoTheta (m : ℕ) (hm : 1 ≤ m) : thetaGraph m ≃g theta m where
  toEquiv := Equiv.optionCongr (thetaEquivAux m)
  map_rel_iff' := by
    rintro (_ | j) (_ | j')
    · exact iff_of_false (fun h => h) (fun h => h)
    · exact theta_adj_none_some_aux m hm j'
    · exact ((theta m).adj_comm _ _).trans (theta_adj_none_some_aux m hm j)
    · exact theta_adj_some_some_aux m hm j j'

/-! ### The classification, restated -/

/-- **The core of `G` is a single vertex**: Mathlib's `⊥` on `Fin 1`.  Equivalently, `G` is a
tree.  First alternative of Rubin's theorem, and of Theorem 2. -/
def CoreIsVertex {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := SimpleGraph.CoreIs G (⊥ : SimpleGraph (Fin 1))

/-- **The core of `G` is a cycle**: Mathlib's `cycleGraph n`, a genuine cycle once `3 ≤ n`.
No parity restriction: Theorem 2 says "is a cycle", not "is an even cycle".  Second alternative
of Theorem 2. -/
def CoreIsCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ n, 3 ≤ n ∧ SimpleGraph.CoreIs G (cycleGraph n)

/-- **The core of `G` is an even cycle.**  Second alternative of Rubin's theorem. -/
def CoreIsEvenCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ n, Even n ∧ 4 ≤ n ∧ SimpleGraph.CoreIs G (cycleGraph n)

/-- **The core of `G` is `θ_{2,2,2m}` for some `m ≥ 1`.**  Third alternative of Rubin's
theorem. -/
def CoreIsTheta {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ m, 1 ≤ m ∧ SimpleGraph.CoreIs G (thetaGraph m)

/-- **The core of `G` is `K₂,₃`**, which is `thetaGraph 1 = θ_{2,2,2}`.  Third alternative of
Theorem 2. -/
def CoreIsK23 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := SimpleGraph.CoreIs G (thetaGraph 1)

/-- **`G` contains an odd cycle**: a subgraph copy of `cycleGraph n` for an odd `n ≥ 3`.  Fourth
alternative of Theorem 2. -/
def HasOddCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ n, Odd n ∧ 3 ≤ n ∧ SimpleGraph.Contains G (cycleGraph n)

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem coreIsVertex_iff : CoreIsVertex G ↔ ListColoring.CoreIsVertex G :=
  ListColoring.coreIs_congr_right ListColoring.botFinOneIsoPathGZero

theorem coreIsCycle_iff : CoreIsCycle G ↔ ListColoring.CoreIsCycle G := by
  constructor
  · rintro ⟨n, hn, h⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ⟨k, by omega,
      (ListColoring.coreIs_congr_right (cycleGraphIsoClosePath k (by omega))).mp h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k + 1, by omega,
      (ListColoring.coreIs_congr_right (cycleGraphIsoClosePath k (by omega))).mpr h⟩

theorem coreIsEvenCycle_iff : CoreIsEvenCycle G ↔ ListColoring.CoreIsEvenCycle G := by
  constructor
  · rintro ⟨n, hev, hn, h⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨t, ht⟩ := hev
    exact ⟨k, ⟨t - 1, by omega⟩, by omega,
      (ListColoring.coreIs_congr_right (cycleGraphIsoClosePath k (by omega))).mp h⟩
  · rintro ⟨k, hodd, hk, h⟩
    obtain ⟨t, ht⟩ := hodd
    exact ⟨k + 1, ⟨t + 1, by omega⟩, by omega,
      (ListColoring.coreIs_congr_right (cycleGraphIsoClosePath k (by omega))).mpr h⟩

theorem coreIsTheta_iff : CoreIsTheta G ↔ ListColoring.CoreIsTheta G := by
  constructor
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, (ListColoring.coreIs_congr_right (thetaGraphIsoTheta m hm)).mp h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m, hm, (ListColoring.coreIs_congr_right (thetaGraphIsoTheta m hm)).mpr h⟩

theorem coreIsK23_iff : CoreIsK23 G ↔ ListColoring.CoreIsK23 G :=
  ListColoring.coreIs_congr_right (thetaGraphIsoTheta 1 le_rfl)

theorem hasOddCycle_iff : HasOddCycle G ↔ ListColoring.HasOddCycle G := by
  constructor
  · rintro ⟨n, hodd, hn, h⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨t, ht⟩ := hodd
    exact ⟨k, ⟨t, by omega⟩, by omega,
      (ListColoring.contains_congr_right (cycleGraphIsoClosePath k (by omega))).mp h⟩
  · rintro ⟨k, hev, hk, h⟩
    obtain ⟨t, ht⟩ := hev
    exact ⟨k + 1, ⟨t, by omega⟩, by omega,
      (ListColoring.contains_congr_right (cycleGraphIsoClosePath k (by omega))).mpr h⟩

/-- **Rubin's theorem**, on Mathlib's graphs.

> A connected graph is `2`-choosable iff its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

A. L. Rubin, in Erdős–Rubin–Taylor, *Choosability in graphs*, Congr. Numer. **26** (1980),
125–157.  The paper cites it; this development proves it. -/
theorem rubinTheorem (hconn : G.Connected) :
    G.Choosable 2 ↔ (CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G) := by
  rw [coreIsVertex_iff, coreIsEvenCycle_iff, coreIsTheta_iff]
  exact ListColoring.rubinTheorem G hconn

/-- **Theorem 2 of Kirov–Naimi, with no hypothesis beyond connectivity**, on Mathlib's graphs.

> A connected graph is 2-monophilic iff its core is a single vertex, is a cycle, is `K₂,₃`, or
> contains an odd cycle.

The paper's wording; "2-monophilic" is `ECCAt G 2`.  Kirov–Naimi, Ars Combin. **124** (2016),
329–340, Theorem 2. -/
theorem ecc_two_iff (hconn : G.Connected) :
    G.ECCAt 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G := by
  rw [coreIsVertex_iff, coreIsCycle_iff, coreIsK23_iff, hasOddCycle_iff]
  exact ListColoring.ecc_two_iff G hconn

end SimpleGraph

#print axioms SimpleGraph.rubinTheorem
#print axioms SimpleGraph.ecc_two_iff
