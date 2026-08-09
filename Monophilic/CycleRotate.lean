/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.CycleTwo

/-!
# Rotating a cycle, and the last case of Theorem 1 at `n = 2`

`Monophilic.CycleTwo` reduces the case `n = 2` of Theorem 1 of Kirov–Naimi, for a cycle on an even
number of vertices, to one configuration: a **non-constant** `2`-list assignment whose two lists at
`pathEnd k` and `pathStart k` — the two ends of the one edge `closePath k` is able to delete — are
**equal**. Kirov–Naimi sidestep that configuration by deleting a *different* edge `vw`, one with
`L v ≠ L w`. Here that choice is implemented by a **rotation automorphism** of the cycle, which
moves any prescribed edge onto the distinguished one.

## Contents

* `Monophilic.pathVtxEquiv` : the numbering `pathVtx k` of the vertices of the path, as an
  equivalence `Fin (k+1) ≃ PathV k` (with a computable inverse `Monophilic.pathIdx`)
* `Monophilic.pathG_adj_pathVtx` : `pathVtx k i ~ pathVtx k j` in `pathG k` iff `|i - j| = 1`
* `Monophilic.closePath_adj_pathVtx` : `pathVtx k i ~ pathVtx k j` in `closePath k` iff `i` and `j`
  are *cyclically* adjacent, `(i + 1) % (k+1) = j ∨ (j + 1) % (k+1) = i`
* `Monophilic.rotIso` : rotation by `r`, an automorphism `closePath k ≃g closePath k`
* `Monophilic.two_le_col_closePath_of_not_const` : **`2 ≤ col(C, L)`** for every non-constant
  `2`-list assignment on a cycle — no parity hypothesis needed
* `Monophilic.two_le_col_closePath_of_ends_eq` : the missing hypothesis `H` of
  `Monophilic.monophilic_closePath_two_of_odd`, proved
* `Monophilic.monophilic_closePath_two` : **the case `n = 2` of Theorem 1**, unconditionally
* `Monophilic.monophilic_closePath_of_two_le` : **Theorem 1 in full**, every cycle is
  `n`-monophilic for every `n ≥ 2`
-/

open Finset

namespace Monophilic

open SimpleGraph

/-! ### The numbering of the vertices of a path, as an equivalence -/

/-- The index of a vertex of the path of length `k`, inverse to `pathVtx k`. -/
def pathIdx : (k : ℕ) → PathV k → ℕ
  | 0, _ => 0
  | _ + 1, none => 0
  | k + 1, some v => pathIdx k v + 1

@[simp] lemma pathIdx_zero (v : PathV 0) : pathIdx 0 v = 0 := rfl

@[simp] lemma pathIdx_none (k : ℕ) : pathIdx (k + 1) none = 0 := rfl

@[simp] lemma pathIdx_some (k : ℕ) (v : PathV k) : pathIdx (k + 1) (some v) = pathIdx k v + 1 := rfl

lemma pathIdx_le : ∀ (k : ℕ) (v : PathV k), pathIdx k v ≤ k
  | 0, _ => le_rfl
  | k + 1, v => by
      match v with
      | none => exact Nat.zero_le _
      | some w => exact Nat.succ_le_succ (pathIdx_le k w)

lemma pathVtx_pathIdx : ∀ (k : ℕ) (v : PathV k), pathVtx k (pathIdx k v) = v
  | 0, v => Subsingleton.elim _ v
  | k + 1, v => by
      match v with
      | none => rfl
      | some w => exact congrArg some (pathVtx_pathIdx k w)

lemma pathIdx_pathVtx {k i : ℕ} (hi : i ≤ k) : pathIdx k (pathVtx k i) = i :=
  pathVtx_inj k _ _ (pathIdx_le k _) hi (pathVtx_pathIdx k (pathVtx k i))

/-- **The numbering of a path is an equivalence** `Fin (k+1) ≃ PathV k`. -/
def pathVtxEquiv (k : ℕ) : Fin (k + 1) ≃ PathV k where
  toFun i := pathVtx k i.val
  invFun v := ⟨pathIdx k v, Nat.lt_succ_of_le (pathIdx_le k v)⟩
  left_inv i := Fin.ext (pathIdx_pathVtx (Nat.lt_succ_iff.mp i.isLt))
  right_inv v := pathVtx_pathIdx k v

@[simp] lemma pathVtxEquiv_apply (k : ℕ) (i : Fin (k + 1)) :
    pathVtxEquiv k i = pathVtx k i.val := rfl

@[simp] lemma pathVtxEquiv_symm_apply (k : ℕ) (v : PathV k) :
    (pathVtxEquiv k).symm v = ⟨pathIdx k v, Nat.lt_succ_of_le (pathIdx_le k v)⟩ := rfl

/-- Every vertex of the cycle is `pathVtx k i` for some index `i : Fin (k+1)`. -/
lemma exists_fin_pathVtx (k : ℕ) (v : PathV k) : ∃ i : Fin (k + 1), pathVtx k i.val = v :=
  ⟨(pathVtxEquiv k).symm v, (pathVtxEquiv k).apply_symm_apply v⟩

/-! ### Adjacency in terms of the numbering -/

lemma pathVtx_eq_iff {k i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) :
    pathVtx k i = pathVtx k j ↔ i = j :=
  ⟨pathVtx_inj k i j hi hj, fun h => by rw [h]⟩

lemma pathVtx_eq_pathEnd_iff {k i : ℕ} (hi : i ≤ k) : pathVtx k i = pathEnd k ↔ i = 0 := by
  rw [← pathVtx_zero k]
  exact pathVtx_eq_iff hi (Nat.zero_le k)

lemma pathVtx_eq_pathStart_iff {k i : ℕ} (hi : i ≤ k) : pathVtx k i = pathStart k ↔ i = k := by
  rw [← pathVtx_last k]
  exact pathVtx_eq_iff hi le_rfl

/-- **Adjacency along the path, in terms of the numbering.** Two numbered vertices of `pathG k` are
adjacent exactly when their numbers differ by one. -/
theorem pathG_adj_pathVtx : ∀ (k i j : ℕ), i ≤ k → j ≤ k →
    ((pathG k).Adj (pathVtx k i) (pathVtx k j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
  intro k
  induction k with
  | zero =>
    intro i j hi hj
    have hi0 : i = 0 := Nat.le_zero.mp hi
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hi0
    subst hj0
    exact iff_of_false (fun h => h) (by omega)
  | succ k ih =>
    intro i j hi hj
    match i, j with
    | 0, 0 => exact iff_of_false (fun h => h) (by omega)
    | 0, j + 1 =>
      have hjk : j ≤ k := by omega
      constructor
      · intro h
        have h' : pathVtx k j = pathEnd k := h
        rw [pathVtx_eq_pathEnd_iff hjk] at h'
        omega
      · intro h
        have hj0 : j = 0 := by omega
        show pathVtx k j = pathEnd k
        rw [pathVtx_eq_pathEnd_iff hjk]
        exact hj0
    | i + 1, 0 =>
      have hik : i ≤ k := by omega
      constructor
      · intro h
        have h' : pathVtx k i = pathEnd k := h
        rw [pathVtx_eq_pathEnd_iff hik] at h'
        omega
      · intro h
        have hi0 : i = 0 := by omega
        show pathVtx k i = pathEnd k
        rw [pathVtx_eq_pathEnd_iff hik]
        exact hi0
    | i + 1, j + 1 =>
      have h := ih i j (by omega) (by omega)
      constructor
      · intro hadj
        have := h.mp (show (pathG k).Adj (pathVtx k i) (pathVtx k j) from hadj)
        omega
      · intro hij
        exact h.mpr (by omega)

/-- Reducing `(i + 1) % (k + 1)` for `i ≤ k`. -/
private lemma succ_mod_succ {k i : ℕ} (hi : i ≤ k) :
    (i + 1) % (k + 1) = if i = k then 0 else i + 1 := by
  by_cases h : i = k
  · subst h
    rw [if_pos rfl, Nat.mod_self]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- **Adjacency around the cycle, in terms of the numbering.** Two numbered vertices of
`closePath k` are adjacent exactly when their numbers are *cyclically* consecutive. -/
theorem closePath_adj_pathVtx {k : ℕ} (hk : 1 ≤ k) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) :
    (closePath k).Adj (pathVtx k i) (pathVtx k j) ↔
      ((i + 1) % (k + 1) = j ∨ (j + 1) % (k + 1) = i) := by
  rw [closePath_adj k, pathG_adj_pathVtx k i j hi hj, ne_eq, pathVtx_eq_iff hi hj,
    pathVtx_eq_pathStart_iff hi, pathVtx_eq_pathEnd_iff hj, pathVtx_eq_pathEnd_iff hi,
    pathVtx_eq_pathStart_iff hj, succ_mod_succ hi, succ_mod_succ hj]
  split_ifs <;> omega

/-! ### Cyclic adjacency in `Fin (k+1)`

Recast in the additive group `Fin (k+1)`, where the rotation is visibly an automorphism. -/

lemma val_add_one {k : ℕ} (hk : 1 ≤ k) (i : Fin (k + 1)) :
    ((i + 1 : Fin (k + 1)) : ℕ) = (i.val + 1) % (k + 1) := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < k + 1 by omega)]

/-- **Adjacency around the cycle, as cyclic successorship in `Fin (k+1)`.** -/
theorem closePath_adj_pathVtx_fin {k : ℕ} (hk : 1 ≤ k) (i j : Fin (k + 1)) :
    (closePath k).Adj (pathVtx k i.val) (pathVtx k j.val) ↔ (i + 1 = j ∨ j + 1 = i) := by
  rw [closePath_adj_pathVtx hk (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt),
    Fin.ext_iff, Fin.ext_iff, val_add_one hk, val_add_one hk]

/-! ### The rotation automorphism -/

/-- Rotating the vertices of the cycle by `r`: the vertex numbered `i` becomes the vertex numbered
`i + r` (mod `k + 1`). -/
def rotEquiv (k : ℕ) (r : Fin (k + 1)) : PathV k ≃ PathV k :=
  (pathVtxEquiv k).symm.trans ((Equiv.addRight r).trans (pathVtxEquiv k))

@[simp] lemma rotEquiv_pathVtx (k : ℕ) (r i : Fin (k + 1)) :
    rotEquiv k r (pathVtx k i.val) = pathVtx k ((i + r : Fin (k + 1)) : ℕ) := by
  show pathVtx k (((pathVtxEquiv k).symm (pathVtx k i.val) + r : Fin (k + 1)) : ℕ) = _
  rw [show (pathVtxEquiv k).symm (pathVtx k i.val) = i from (pathVtxEquiv k).symm_apply_apply i]

/-- The rotation in terms of unbounded indices. -/
lemma rotEquiv_pathVtx' (k : ℕ) (r : Fin (k + 1)) {m : ℕ} (hm : m ≤ k) :
    rotEquiv k r (pathVtx k m) = pathVtx k ((m + r.val) % (k + 1)) := by
  have h : m = (⟨m, by omega⟩ : Fin (k + 1)).val := rfl
  rw [h, rotEquiv_pathVtx k r ⟨m, by omega⟩, Fin.val_add]

/-- **The rotation is an automorphism of the cycle.** -/
def rotIso {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1)) : closePath k ≃g closePath k where
  toEquiv := rotEquiv k r
  map_rel_iff' := by
    intro a b
    obtain ⟨i, rfl⟩ := exists_fin_pathVtx k a
    obtain ⟨j, rfl⟩ := exists_fin_pathVtx k b
    show (closePath k).Adj (rotEquiv k r (pathVtx k i.val)) (rotEquiv k r (pathVtx k j.val)) ↔ _
    rw [rotEquiv_pathVtx, rotEquiv_pathVtx, closePath_adj_pathVtx_fin hk,
      closePath_adj_pathVtx_fin hk, add_right_comm i r 1, add_right_comm j r 1, add_left_inj,
      add_left_inj]

@[simp] lemma rotIso_apply {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1)) (v : PathV k) :
    rotIso hk r v = rotEquiv k r v := rfl

/-! ### Sanity checks on the rotation -/

#guard ∀ r : Fin 4, ∀ i : Fin 4, rotEquiv 3 r (pathVtx 3 i.val) = pathVtx 3 ((i.val + r.val) % 4)
#guard ∀ r : Fin 5, ∀ i : Fin 5, rotEquiv 4 r (pathVtx 4 i.val) = pathVtx 4 ((i.val + r.val) % 5)
#guard rotEquiv 3 2 (pathVtx 3 3) = pathVtx 3 1
#guard ∀ r : Fin 4, ∀ i : Fin 4, ∀ j : Fin 4,
    ((closePath 3).Adj (rotEquiv 3 r (pathVtx 3 i.val)) (rotEquiv 3 r (pathVtx 3 j.val))
      ↔ (closePath 3).Adj (pathVtx 3 i.val) (pathVtx 3 j.val))
#guard ∀ i : Fin 4, ∀ j : Fin 4,
    ((closePath 3).Adj (pathVtx 3 i.val) (pathVtx 3 j.val)
      ↔ ((i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val))

/-! The rotation used below, for the edge `pathVtx k i — pathVtx k (i+1)`: rotating by `i + 1`
takes `pathEnd k` to `pathVtx k (i+1)` and `pathStart k` to `pathVtx k i`. -/

#guard rotEquiv 3 2 (pathEnd 3) = pathVtx 3 2      -- `k = 3`, `i = 1`
#guard rotEquiv 3 2 (pathStart 3) = pathVtx 3 1
#guard rotEquiv 5 3 (pathEnd 5) = pathVtx 5 3      -- `k = 5`, `i = 2`
#guard rotEquiv 5 3 (pathStart 5) = pathVtx 5 2

/-! ### Some edge of the cycle has different lists at its two ends

A list assignment all of whose consecutive vertices carry the same list is constant. -/

lemma const_of_consecutive_eq {k : ℕ} {L : ListAssignment (PathV k)}
    (h : ∀ i, i < k → L (pathVtx k i) = L (pathVtx k (i + 1))) :
    ∀ i, i ≤ k → L (pathVtx k i) = L (pathEnd k) := by
  intro i
  induction i with
  | zero => intro _; rw [pathVtx_zero]
  | succ n ih =>
    intro hn
    rw [← h n (by omega)]
    exact ih (by omega)

/-- **A non-constant assignment differs across some edge of the path.** -/
lemma exists_consecutive_list_ne {k : ℕ} {L : ListAssignment (PathV k)}
    (hnc : ∃ v, L v ≠ L (pathEnd k)) :
    ∃ i, i < k ∧ L (pathVtx k i) ≠ L (pathVtx k (i + 1)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := hnc
  obtain ⟨i, hi, rfl⟩ := exists_pathVtx k v
  exact hv (const_of_consecutive_eq hcon i hi)

/-! ### The payoff: the last case of `n = 2` -/

/-- **`2 ≤ col(C, L)` for every non-constant `2`-list assignment on a cycle.**

This is Case 2 of Kirov–Naimi p. 5–6 with their choice of edge restored: some edge of the cycle has
different lists at its two ends, and a rotation `Monophilic.rotIso` carries that edge onto the
distinguished edge `pathEnd k — pathStart k`, where
`Monophilic.two_le_col_closePath_of_ends_ne` applies. No parity hypothesis is needed. -/
theorem two_le_col_closePath_of_not_const {k : ℕ} (hk : 1 ≤ k) {L : ListAssignment (PathV k)}
    (hcard : ∀ v, (L v).card = 2) (hnc : ∃ v, L v ≠ L (pathEnd k)) :
    2 ≤ (closePath k).col L := by
  obtain ⟨i, hik, hne⟩ := exists_consecutive_list_ne hnc
  have hlt : i + 1 < k + 1 := by omega
  -- rotate by `i + 1`, taking `pathEnd k` to `pathVtx k (i+1)` and `pathStart k` to `pathVtx k i`
  let r : Fin (k + 1) := ⟨i + 1, hlt⟩
  have hrv : (r : ℕ) = i + 1 := rfl
  let e : closePath k ≃g closePath k := rotIso hk r
  have hLe : ∀ m : ℕ, m ≤ k →
      L (e (pathVtx k m)) = L (pathVtx k ((m + (i + 1)) % (k + 1))) := by
    intro m hm
    show L (rotEquiv k r (pathVtx k m)) = _
    rw [rotEquiv_pathVtx' k r hm, hrv]
  have h1 : L (e (pathEnd k)) = L (pathVtx k (i + 1)) := by
    rw [← pathVtx_zero k, hLe 0 (Nat.zero_le k), Nat.zero_add, Nat.mod_eq_of_lt hlt]
  have h2 : L (e (pathStart k)) = L (pathVtx k i) := by
    rw [← pathVtx_last k, hLe k le_rfl, show k + (i + 1) = (k + 1) + i by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have key : 2 ≤ (closePath k).col (L ∘ e) := by
    refine two_le_col_closePath_of_ends_ne hk (fun v => hcard _) ?_
    simp only [Function.comp_apply]
    rw [h1, h2]
    exact fun h => hne h.symm
  rwa [col_comp_iso e L] at key

/-- The hypothesis `H` of `Monophilic.monophilic_closePath_two_of_odd`, now proved: a non-constant
`2`-list assignment whose two lists at the ends of the distinguished edge are *equal* still admits
at least two colorings of the cycle. -/
theorem two_le_col_closePath_of_ends_eq {k : ℕ} (hk : 1 ≤ k) {L : ListAssignment (PathV k)}
    (hcard : ∀ v, (L v).card = 2) (_hends : L (pathEnd k) = L (pathStart k))
    (hnc : ∃ v, L v ≠ L (pathEnd k)) : 2 ≤ (closePath k).col L :=
  two_le_col_closePath_of_not_const hk hcard hnc

/-- **The case `n = 2` of Theorem 1 of Kirov–Naimi.** A cycle on an even number of vertices is
`2`-monophilic; `closePath k` has `k + 1` vertices, so `Odd k` says that number is even. -/
theorem monophilic_closePath_two {k : ℕ} (hk : Odd k) : (closePath k).Monophilic 2 :=
  monophilic_closePath_two_of_odd hk fun _ hcard _ hnc =>
    two_le_col_closePath_of_not_const hk.pos hcard hnc

/-- **Theorem 1 of Kirov–Naimi in full: every cycle is `n`-monophilic, for every `n ≥ 2`.**

`closePath k` is the cycle on `k + 1` vertices, so `2 ≤ k` says it has at least three. For `n ≥ 3`
this is `Monophilic.monophilic_closePath`; the case `n = 2` splits into an odd number of vertices
(`Monophilic.monophilic_closePath_of_odd`, where `col(C, 2) = 0`) and an even number of vertices
(`Monophilic.monophilic_closePath_two`). -/
theorem monophilic_closePath_of_two_le {k m : ℕ} (hk : 2 ≤ k) :
    (closePath k).Monophilic (m + 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.even_or_odd k with hev | hodd
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : Odd j := by
        rcases Nat.even_or_odd j with h | h
        · exact absurd h (Nat.even_add_one.mp hev)
        · exact h
      exact monophilic_closePath_of_odd hj 0
    · exact monophilic_closePath_two hodd
  · exact monophilic_closePath hk hm

end Monophilic

#print axioms Monophilic.pathVtxEquiv
#print axioms Monophilic.pathG_adj_pathVtx
#print axioms Monophilic.closePath_adj_pathVtx
#print axioms Monophilic.closePath_adj_pathVtx_fin
#print axioms Monophilic.rotIso
#print axioms Monophilic.two_le_col_closePath_of_not_const
#print axioms Monophilic.two_le_col_closePath_of_ends_eq
#print axioms Monophilic.monophilic_closePath_two
#print axioms Monophilic.monophilic_closePath_of_two_le
