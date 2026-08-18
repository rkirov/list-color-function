/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.C6Branch

/-!
# `EvenCycleBranchLarge` — the general `m ≥ 7` branch of `cycle_gm_bound_even`

The handoff's §5.3–§5.6 chain, for an even cycle `C_{2(M+1)}` with `M ≥ 3` terminals-minus-one
(Lean `m = 2M+1 ≥ 7`), at a **non-identity** holonomy.  The identity holonomy is
`cycle_gm_bound_even_identity`.

Layer 1 (this section) is the scalar comparison of handoff §5.5: the entropy denominator
`∏_a U^U` against the budget `2^(6 m T)` times **one** strict path factor `C^T = (729/256)^T`
harvested at an ordinary internal vertex whose two terminal enumerations differ.
-/

namespace ListColoring

open Finset

/-! ## §5.5 — the two scalar comparisons -/

theorem two_gammaPlus_succ (N : ℕ) : 2 * gammaPlus (N + 1) = 8 * gammaPlus N + 2 := by
  rw [gammaPlus_succ]; ring

/-- `16 · 256^k ≤ 729^k` for `k ≥ 4`: four `(2,1)` blocks of the strict factor `C = 729/256`
already clear `2^4`. -/
theorem sixteen_mul_pow_le : ∀ k : ℕ, 4 ≤ k → 16 * 256 ^ k ≤ 729 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc 16 * 256 ^ (k + 1) = 256 * (16 * 256 ^ k) := by ring
      _ ≤ 256 * 729 ^ k := Nat.mul_le_mul_left _ ih
      _ ≤ 729 * 729 ^ k := Nat.mul_le_mul_right _ (by norm_num)
      _ = 729 ^ (k + 1) := by ring

theorem eight_mul_pow_le {k : ℕ} (hk : 4 ≤ k) : 8 * 256 ^ k ≤ 729 ^ k :=
  le_trans (Nat.mul_le_mul_right _ (by norm_num)) (sixteen_mul_pow_le k hk)

/-- The three-cycle induction step in the scalar variables `q = 2^N`, `g = γ_N`. -/
theorem entropy_step_three (q g : ℕ) (hq : 1 ≤ q) (hg : 4 ≤ 3 * g + 1)
    (ih : (q + 1) ^ (3 * (q + 1)) * 256 ^ g ≤ q ^ (3 * q) * 729 ^ g) :
    (2 * q + 1) ^ (3 * (2 * q + 1)) * 256 ^ (4 * g + 1)
      ≤ (2 * q) ^ (3 * (2 * q)) * 729 ^ (4 * g + 1) := by
  have e : ((2 * q) ^ q * (2 * q + 2) ^ (q + 1)) ^ 3
      = 2 ^ (6 * q + 3) * q ^ (3 * q) * (q + 1) ^ (3 * (q + 1)) := by
    rw [show 2 * q + 2 = 2 * (q + 1) from by ring]
    simp only [mul_pow]
    ring
  have hA : (2 * q + 1) ^ (3 * (2 * q + 1))
      ≤ 2 ^ (6 * q + 3) * q ^ (3 * q) * (q + 1) ^ (3 * (q + 1)) := by
    rw [← e]
    calc (2 * q + 1) ^ (3 * (2 * q + 1)) = ((2 * q + 1) ^ (2 * q + 1)) ^ 3 := by ring
      _ ≤ ((2 * q) ^ q * (2 * q + 2) ^ (q + 1)) ^ 3 :=
          Nat.pow_le_pow_left (le_of_lt (delta_step q hq)) 3
  calc (2 * q + 1) ^ (3 * (2 * q + 1)) * 256 ^ (4 * g + 1)
      ≤ (2 ^ (6 * q + 3) * q ^ (3 * q) * (q + 1) ^ (3 * (q + 1))) * 256 ^ (4 * g + 1) :=
        Nat.mul_le_mul_right _ hA
    _ = 2 ^ (6 * q + 3) * q ^ (3 * q) * 256 ^ (3 * g + 1) *
          ((q + 1) ^ (3 * (q + 1)) * 256 ^ g) := by ring
    _ ≤ 2 ^ (6 * q + 3) * q ^ (3 * q) * 256 ^ (3 * g + 1) * (q ^ (3 * q) * 729 ^ g) :=
        Nat.mul_le_mul_left _ ih
    _ = 2 ^ (6 * q) * q ^ (6 * q) * 729 ^ g * (8 * 256 ^ (3 * g + 1)) := by ring
    _ ≤ 2 ^ (6 * q) * q ^ (6 * q) * 729 ^ g * 729 ^ (3 * g + 1) :=
        Nat.mul_le_mul_left _ (eight_mul_pow_le hg)
    _ = (2 * q) ^ (3 * (2 * q)) * 729 ^ (4 * g + 1) := by
        simp only [mul_pow]; ring

/-- The transposition induction step. -/
theorem entropy_step_trans (q g n : ℕ) (hq : 1 ≤ q) (hg : 4 ≤ 3 * g + 1)
    (ih : (q + 1) ^ (2 * (q + 1)) * 2 ^ (2 * n + 8) * 256 ^ g ≤ q ^ (2 * q) * 729 ^ g) :
    (2 * q + 1) ^ (2 * (2 * q + 1)) * 2 ^ (2 * (n + 1) + 8) * 256 ^ (4 * g + 1)
      ≤ (2 * q) ^ (2 * (2 * q)) * 729 ^ (4 * g + 1) := by
  have e : ((2 * q) ^ q * (2 * q + 2) ^ (q + 1)) ^ 2
      = 2 ^ (4 * q + 2) * q ^ (2 * q) * (q + 1) ^ (2 * (q + 1)) := by
    rw [show 2 * q + 2 = 2 * (q + 1) from by ring]
    simp only [mul_pow]
    ring
  have hA : (2 * q + 1) ^ (2 * (2 * q + 1))
      ≤ 2 ^ (4 * q + 2) * q ^ (2 * q) * (q + 1) ^ (2 * (q + 1)) := by
    rw [← e]
    calc (2 * q + 1) ^ (2 * (2 * q + 1)) = ((2 * q + 1) ^ (2 * q + 1)) ^ 2 := by ring
      _ ≤ ((2 * q) ^ q * (2 * q + 2) ^ (q + 1)) ^ 2 :=
          Nat.pow_le_pow_left (le_of_lt (delta_step q hq)) 2
  calc (2 * q + 1) ^ (2 * (2 * q + 1)) * 2 ^ (2 * (n + 1) + 8) * 256 ^ (4 * g + 1)
      ≤ (2 ^ (4 * q + 2) * q ^ (2 * q) * (q + 1) ^ (2 * (q + 1))) *
          2 ^ (2 * (n + 1) + 8) * 256 ^ (4 * g + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA)
    _ = 2 ^ (4 * q + 4) * q ^ (2 * q) * 256 ^ (3 * g + 1) *
          ((q + 1) ^ (2 * (q + 1)) * 2 ^ (2 * n + 8) * 256 ^ g) := by ring
    _ ≤ 2 ^ (4 * q + 4) * q ^ (2 * q) * 256 ^ (3 * g + 1) * (q ^ (2 * q) * 729 ^ g) :=
        Nat.mul_le_mul_left _ ih
    _ = 2 ^ (4 * q) * q ^ (4 * q) * 729 ^ g * (16 * 256 ^ (3 * g + 1)) := by ring
    _ ≤ 2 ^ (4 * q) * q ^ (4 * q) * 729 ^ g * 729 ^ (3 * g + 1) :=
        Nat.mul_le_mul_left _ (sixteen_mul_pow_le _ hg)
    _ = (2 * q) ^ (2 * (2 * q)) * 729 ^ (4 * g + 1) := by
        simp only [mul_pow]; ring

theorem four_le_three_gammaPlus {N : ℕ} (hN : 2 ≤ N) : 4 ≤ 3 * gammaPlus N + 1 := by
  have h1 := three_mul_gammaPlus_add_one N
  have h2 : (4 : ℕ) ^ 2 ≤ 4 ^ N := Nat.pow_le_pow_right (by omega) hN
  norm_num at h2
  omega

/-- **(5.16)** — the three-cycle comparison: the entropy correction `3 Δ(q)` of the three moved
constant words is paid by one strict path factor `C^T`. -/
theorem entropy_three_cycle_bound : ∀ N : ℕ, 3 ≤ N →
    (2 ^ N + 1) ^ (3 * (2 ^ N + 1)) * 256 ^ gammaPlus N
      ≤ (2 ^ N) ^ (3 * 2 ^ N) * 729 ^ gammaPlus N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num [gammaPlus]
  | succ N hN ih =>
    have h2 : (2:ℕ) ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
    rw [h2, gammaPlus_succ]
    exact entropy_step_three (2 ^ N) (gammaPlus N) Nat.one_le_two_pow
      (four_le_three_gammaPlus (by omega)) ih

/-- **(5.17)** — the transposition comparison: the `2 Δ(q)` correction, the `2m` from `f = 1`
and the `2^6` seam repair are all paid by one strict path factor `C^T`. -/
theorem entropy_transposition_bound : ∀ N : ℕ, 3 ≤ N →
    (2 ^ N + 1) ^ (2 * (2 ^ N + 1)) * 2 ^ (2 * N + 8) * 256 ^ gammaPlus N
      ≤ (2 ^ N) ^ (2 * 2 ^ N) * 729 ^ gammaPlus N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num [gammaPlus]
  | succ N hN ih =>
    have h2 : (2:ℕ) ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
    rw [h2, gammaPlus_succ]
    exact entropy_step_trans (2 ^ N) (gammaPlus N) N Nat.one_le_two_pow
      (four_le_three_gammaPlus (by omega)) ih

end ListColoring

/-! ## §5.4 — the entropy denominator at a general holonomy -/

namespace ListColoring
namespace RefTensor

open Finset

variable {N : ℕ}

/-- `h` in the wrap-around presentation, as a sum of edge indicators. -/
theorem hw_eq_sum_edges (σ : Equiv.Perm (Fin 3)) (a : Fin (N + 1) → Fin 3) :
    hw σ a = ∑ i : Fin (N + 1),
      (if a (i + 1) = (if i = Fin.last N then σ (a i) else a i) then 1 else 0) := by
  rw [← hwCyc_eq_hw, hwCyc, Finset.card_filter]

/-- Fibering a pinned edge sum over the value at the tail. -/
theorem sum_pin_fiber (s t : Fin (N + 1)) (φ : Fin 3 → Fin 3)
    (F : (Fin (N + 1) → Fin 3) → ℕ) :
    (∑ a : Fin (N + 1) → Fin 3, (if a t = φ (a s) then F a else 0))
      = ∑ c : Fin 3, ∑ a ∈ univ.filter
          (fun a : Fin (N + 1) → Fin 3 => (a s, a t) = (c, φ c)), F a := by
  classical
  have hstep : ∀ c : Fin 3,
      (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a s, a t) = (c, φ c)), F a)
        = ∑ a : Fin (N + 1) → Fin 3, (if a s = c ∧ a t = φ c then F a else 0) := by
    intro c
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ => by simp only [Prod.mk.injEq]
  rw [Finset.sum_congr rfl (fun c _ => hstep c), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (a s)]
  · by_cases h : a t = φ (a s) <;> simp [h]
  · intro c _ hc
    exact if_neg (fun hh => hc hh.1.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_pin_fiber_id (s t : Fin (N + 1)) (F : (Fin (N + 1) → Fin 3) → ℕ) :
    (∑ a : Fin (N + 1) → Fin 3, (if a t = a s then F a else 0))
      = ∑ c : Fin 3, ∑ a ∈ univ.filter
          (fun a : Fin (N + 1) → Fin 3 => (a s, a t) = (c, c)), F a :=
  sum_pin_fiber s t (fun c => c) F

/-- The pinned constant-word correction: only the constant word can contribute. -/
theorem corr_pin (σ : Equiv.Perm (Fin 3)) (s t : Fin (N + 1)) (p q : Fin 3) :
    (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a s, a t) = (p, q)),
        (if (∀ j, a j = a 0) ∧ σ (a 0) ≠ a 0 then 1 else 0))
      = if p = q ∧ σ p ≠ p then 1 else 0 := by
  classical
  rw [← Finset.card_filter]
  by_cases hpq : p = q ∧ σ p ≠ p
  · obtain ⟨heq, hmv⟩ := hpq
    subst heq
    rw [if_pos ⟨rfl, hmv⟩]
    have hset : (univ.filter (fun a : Fin (N + 1) → Fin 3 => (a s, a t) = (p, p))).filter
        (fun a => (∀ j, a j = a 0) ∧ σ (a 0) ≠ a 0) = {fun _ => p} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, -⟩, hconst, -⟩
        have h0 : a 0 = p := by rw [← hconst s]; exact h1
        funext j; rw [hconst j, h0]
      · rintro rfl
        exact ⟨⟨rfl, rfl⟩, fun j => rfl, hmv⟩
    rw [hset, Finset.card_singleton]
  · rw [if_neg hpq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a ha ⟨hconst, hmv⟩
    rw [Finset.mem_filter] at ha
    obtain ⟨-, hst⟩ := ha
    have h1 : a s = p := congrArg Prod.fst hst
    have h2 : a t = q := congrArg Prod.snd hst
    have hp : a 0 = p := by rw [← hconst s]; exact h1
    have hq : a 0 = q := by rw [← hconst t]; exact h2
    refine hpq ⟨hp ▸ hq, ?_⟩
    rw [hp] at hmv; exact hmv

/-- `2 ^ h` on a pinned cell is the `U`-mass minus the constant-word correction. -/
theorem cell_two_pow (σ : Equiv.Perm (Fin 3)) (s t : Fin (N + 1)) (p q : Fin 3) :
    ((∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a s, a t) = (p, q)), 2 ^ hw σ a)
        + (if p = q ∧ σ p ≠ p then 1 else 0))
      = ∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a s, a t) = (p, q)), Uw σ a := by
  classical
  rw [← corr_pin σ s t p q, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- **Every cyclic edge carries exactly `6 γ_N + 2 f` of the bare `2^h` mass**, uniformly in the
holonomy `σ` and in the edge — the general-`σ` companion of `edge_mass_one`. -/
theorem edge_mass (σ : Equiv.Perm (Fin 3)) (i : Fin (N + 1)) :
    (∑ a : Fin (N + 1) → Fin 3,
        (if a (i + 1) = (if i = Fin.last N then σ (a i) else a i) then 2 ^ hw σ a else 0))
      = 6 * gammaPlus N + 2 * fixCount σ := by
  classical
  have hfin : ∀ f : Fin 3 → ℕ, (∀ c, f c = 2 * gammaPlus N + 2 * (if σ c = c then 1 else 0)) →
      (∑ c : Fin 3, f c) = 6 * gammaPlus N + 2 * fixCount σ := by
    intro f hf
    rw [Finset.sum_congr rfl (fun c _ => hf c), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum, ← fixCount_eq_sum]
    ring
  by_cases hlast : i = Fin.last N
  · subst hlast
    have hIf : ∀ a : Fin (N + 1) → Fin 3,
        (if a (Fin.last N + 1) =
            (if (Fin.last N : Fin (N + 1)) = Fin.last N then σ (a (Fin.last N))
              else a (Fin.last N)) then 2 ^ hw σ a else 0)
          = (if a (Fin.last N + 1) = σ (a (Fin.last N)) then 2 ^ hw σ a else 0) := by
      intro a; simp
    rw [Finset.sum_congr rfl (fun a _ => hIf a),
      sum_pin_fiber (Fin.last N) (Fin.last N + 1) (fun c => σ c) (fun a => 2 ^ hw σ a)]
    refine hfin _ fun c => ?_
    have hz : (Fin.last N : Fin (N + 1)) + 1 = 0 := by apply Fin.ext; simp
    have hc := cell_two_pow σ (Fin.last N) (Fin.last N + 1) c (σ c)
    have hzero : (if c = σ c ∧ σ c ≠ c then (1:ℕ) else 0) = 0 := by
      rw [if_neg]; rintro ⟨h1, h2⟩; exact h2 h1.symm
    rw [hzero, add_zero] at hc
    have hres : resClose σ c c = 2 * (if σ c = c then 1 else 0) := by
      simp only [resClose, Matrix.of_apply]
      by_cases h : σ c = c
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun hh : c = σ c => h hh.symm), if_neg h]
    rw [hc, hz, pairMarginal_closing σ c c, if_pos rfl, hres]
  · have hi : i.val + 1 < N + 1 := by
      have h1 : i.val ≤ N := by omega
      have h2 : i.val ≠ N := fun hh => hlast (Fin.ext hh)
      omega
    have hIf : ∀ a : Fin (N + 1) → Fin 3,
        (if a (i + 1) = (if i = Fin.last N then σ (a i) else a i) then 2 ^ hw σ a else 0)
          = (if a (i + 1) = a i then 2 ^ hw σ a else 0) := by
      intro a; rw [if_neg hlast]
    rw [Finset.sum_congr rfl (fun a _ => hIf a), sum_pin_fiber_id i (i + 1) (fun a => 2 ^ hw σ a)]
    refine hfin _ fun c => ?_
    have hc := cell_two_pow σ i (i + 1) c c
    have hres : resOrd σ c c = 1 + (if σ c = c then 1 else 0) := by
      simp only [resOrd, Matrix.of_apply]
      by_cases h : σ c = c
      · simp [h]
      · simp only [h, if_false]
        rw [if_neg (fun hh : c = σ c => h hh.symm)]
        simp
    rw [pairMarginal_ordinary σ i hi c c, if_pos rfl, hres] at hc
    by_cases h : σ c = c
    · rw [if_neg (by rintro ⟨-, h2⟩; exact h2 h), if_pos h] at hc
      rw [if_pos h]; omega
    · rw [if_pos ⟨rfl, h⟩, if_neg h] at hc
      rw [if_neg h]; omega

/-- **The entropy sum `∑_a h(a) 2^{h(a)}` at a general holonomy** (handoff (5.6) before the
`Δ` correction): `m (6 γ_N + 2 f)` with `m = N + 1` terminals and `f = fix σ`. -/
theorem sum_two_pow_hw_mul_hw_gen (σ : Equiv.Perm (Fin 3)) :
    (∑ a : Fin (N + 1) → Fin 3, 2 ^ hw σ a * hw σ a)
      = (N + 1) * (6 * gammaPlus N + 2 * fixCount σ) := by
  classical
  have hexp : ∀ a : Fin (N + 1) → Fin 3,
      2 ^ hw σ a * hw σ a
        = ∑ i : Fin (N + 1),
            (if a (i + 1) = (if i = Fin.last N then σ (a i) else a i) then 2 ^ hw σ a
              else 0) := by
    intro a
    rw [hw_eq_sum_edges σ a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : a (i + 1) = (if i = Fin.last N then σ (a i) else a i) <;> simp [h]
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => edge_mass σ i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end RefTensor
end ListColoring

namespace ListColoring
namespace RefTensor

open Finset

variable {N : ℕ}

/-- The moved constant words: the only place where `U` is not a power of two. -/
def movedConst (σ : Equiv.Perm (Fin 3)) : Finset (Fin (N + 1) → Fin 3) :=
  univ.filter (fun a : Fin (N + 1) → Fin 3 => (∀ j, a j = a 0) ∧ σ (a 0) ≠ a 0)

theorem mem_movedConst {σ : Equiv.Perm (Fin 3)} {a : Fin (N + 1) → Fin 3} :
    a ∈ movedConst σ ↔ (∀ j, a j = a 0) ∧ σ (a 0) ≠ a 0 := by
  simp [movedConst]

/-- `h` of a moved constant word is `N`: all `N` ordinary edges match, the closing one does not. -/
theorem hw_const_moved (σ : Equiv.Perm (Fin 3)) (c : Fin 3) (hc : σ c ≠ c) :
    hw σ (fun _ : Fin (N + 1) => c) = N := by
  unfold hw
  have h1 : (univ.filter fun i : Fin N => (fun _ : Fin (N + 1) => c) i.castSucc
      = (fun _ : Fin (N + 1) => c) i.succ) = univ := by
    apply Finset.filter_true_of_mem
    intro i _; rfl
  rw [h1, Finset.card_univ, Fintype.card_fin, if_neg (by simpa using fun hh => hc hh.symm)]
  omega

theorem Uw_of_mem_movedConst {σ : Equiv.Perm (Fin 3)} {a : Fin (N + 1) → Fin 3}
    (ha : a ∈ movedConst σ) : Uw σ a = 2 ^ N + 1 := by
  rw [mem_movedConst] at ha
  have hconst : a = fun _ => a 0 := funext ha.1
  unfold Uw
  rw [if_pos ha]
  congr 1
  rw [hconst, hw_const_moved σ (a 0) ha.2]

theorem Uw_of_not_mem_movedConst {σ : Equiv.Perm (Fin 3)} {a : Fin (N + 1) → Fin 3}
    (ha : a ∉ movedConst σ) : Uw σ a = 2 ^ hw σ a := by
  rw [mem_movedConst] at ha
  unfold Uw
  rw [if_neg ha, add_zero]

/-- There are `3 - f` moved constant words. -/
theorem card_movedConst_add_fixCount (σ : Equiv.Perm (Fin 3)) :
    (movedConst (N := N) σ).card + fixCount σ = 3 := by
  classical
  have himg : movedConst (N := N) σ
      = (univ.filter fun c : Fin 3 => σ c ≠ c).image
          (fun c => (fun _ : Fin (N + 1) => c)) := by
    ext a
    simp only [mem_movedConst, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hconst, hmv⟩
      exact ⟨a 0, hmv, (funext hconst).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨fun j => rfl, hc⟩
  have hinj : Function.Injective (fun c : Fin 3 => (fun _ : Fin (N + 1) => c)) := by
    intro c d h
    exact congrFun h 0
  rw [himg, Finset.card_image_of_injective _ hinj, fixCount]
  have hcompl : (univ.filter fun c : Fin 3 => σ c ≠ c)
      = (univ.filter fun c : Fin 3 => σ c = c)ᶜ := by
    ext c; simp
  rw [hcompl, Finset.card_compl, Fintype.card_fin]
  have hle : (univ.filter fun c : Fin 3 => σ c = c).card ≤ 3 := by
    have h := Finset.card_filter_le (univ : Finset (Fin 3)) (fun c => σ c = c)
    simpa using h
  omega

/-- **The entropy denominator at a general holonomy** (handoff (5.6)): a power of two times
`((q+1)^{q+1})^{3-f}` with `q = 2^N` — the `Δ(q)` corrections of the moved constant words. -/
theorem prod_Uw_pow_Uw_gen (σ : Equiv.Perm (Fin 3)) :
    (∏ a : Fin (N + 1) → Fin 3, Uw σ a ^ Uw σ a) *
        2 ^ ((movedConst (N := N) σ).card * (2 ^ N * N))
      = ((2 ^ N + 1) ^ (2 ^ N + 1)) ^ (movedConst (N := N) σ).card *
          2 ^ ((N + 1) * (6 * gammaPlus N + 2 * fixCount σ)) := by
  classical
  set S : Finset (Fin (N + 1) → Fin 3) := movedConst σ with hS
  have hsplit : (∏ a : Fin (N + 1) → Fin 3, Uw σ a ^ Uw σ a)
      = (∏ a ∈ S, Uw σ a ^ Uw σ a) * ∏ a ∈ Sᶜ, Uw σ a ^ Uw σ a := by
    rw [← Finset.prod_mul_prod_compl S (fun a => Uw σ a ^ Uw σ a)]
  have hS1 : (∏ a ∈ S, Uw σ a ^ Uw σ a) = ((2 ^ N + 1) ^ (2 ^ N + 1)) ^ S.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun a ha => by rw [Uw_of_mem_movedConst (hS ▸ ha)]
  have hS2 : (∏ a ∈ Sᶜ, Uw σ a ^ Uw σ a) = 2 ^ (∑ a ∈ Sᶜ, 2 ^ hw σ a * hw σ a) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a ha => ?_
    have hna : a ∉ S := (Finset.mem_compl).mp ha
    rw [Uw_of_not_mem_movedConst (hS ▸ hna), ← pow_mul, Nat.mul_comm]
  have hSsum : (∑ a ∈ S, 2 ^ hw σ a * hw σ a) = S.card * (2 ^ N * N) := by
    have hval : ∀ a ∈ S, 2 ^ hw σ a * hw σ a = 2 ^ N * N := by
      intro a ha
      have ha' := (hS ▸ ha : a ∈ movedConst σ)
      rw [mem_movedConst] at ha'
      have hconst : a = fun _ => a 0 := funext ha'.1
      rw [hconst, hw_const_moved σ (a 0) ha'.2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul]
  have htotal : (∑ a ∈ S, 2 ^ hw σ a * hw σ a) + (∑ a ∈ Sᶜ, 2 ^ hw σ a * hw σ a)
      = (N + 1) * (6 * gammaPlus N + 2 * fixCount σ) := by
    rw [Finset.sum_add_sum_compl, sum_two_pow_hw_mul_hw_gen σ]
  rw [hsplit, hS1, hS2, mul_assoc, ← pow_add]
  rw [show (∑ a ∈ Sᶜ, 2 ^ hw σ a * hw σ a) + S.card * (2 ^ N * N)
        = (N + 1) * (6 * gammaPlus N + 2 * fixCount σ) by rw [← hSsum]; omega]

end RefTensor
end ListColoring


namespace ListColoring

open Finset

variable {Z : Finset ℕ} {x : ℕ → ℕ} {A B : Fin 3 → ℕ}

/-! ## The pair product carrying an exponent matrix -/

/-- `∏_{p,q} N(A p, B q) ^ D(p,q)`: the shape the internal factors take after
`RefTensor.pair_exponent`. -/
def pairProd (Z : Finset ℕ) (x : ℕ → ℕ) (A B : Fin 3 → ℕ) (D : Fin 3 → Fin 3 → ℕ) : ℕ :=
  ∏ pq : Fin 3 × Fin 3, pathN Z x (A pq.1) (B pq.2) ^ D pq.1 pq.2

theorem pairProd_add (D E : Fin 3 → Fin 3 → ℕ) :
    pairProd Z x A B (fun p q => D p q + E p q)
      = pairProd Z x A B D * pairProd Z x A B E := by
  unfold pairProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun pq _ => pow_add _ _ _

theorem pairProd_two (D : Fin 3 → Fin 3 → ℕ) :
    pairProd Z x A B (fun p q => 2 * D p q) = pairProd Z x A B D ^ 2 := by
  unfold pairProd
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun pq _ => by rw [← pow_mul, mul_comm]

/-- The all-cells product is `pathDiag · pathOff`. -/
theorem prod_all_cells :
    (∏ pq : Fin 3 × Fin 3, pathN Z x (A pq.1) (B pq.2))
      = pathDiag Z x A B * pathOff Z x A B := by
  rw [Fintype.prod_prod_type, pathDiag_eq, pathOff_eq]
  simp only [Fin.prod_univ_three]
  ring

theorem pairProd_const (T : ℕ) :
    pairProd Z x A B (fun _ _ => T) = (pathDiag Z x A B * pathOff Z x A B) ^ T := by
  unfold pairProd
  rw [Finset.prod_pow, prod_all_cells]

/-- A permutation matrix of exponents selects the corresponding generalized diagonal. -/
theorem pairProd_perm (τ : Equiv.Perm (Fin 3)) :
    pairProd Z x A B (fun p q => if p = τ q then 1 else 0)
      = ∏ q : Fin 3, pathN Z x (A (τ q)) (B q) := by
  unfold pairProd
  rw [Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hstep : ∀ p : Fin 3, pathN Z x (A p) (B q) ^ (if p = τ q then 1 else 0)
      = if p = τ q then pathN Z x (A p) (B q) else 1 := by
    intro p; split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun p _ => hstep p),
    Finset.prod_ite_eq' univ (τ q) (fun p => pathN Z x (A p) (B q))]
  simp

theorem pairProd_id_perm :
    pairProd Z x A B (fun p q => if p = q then 1 else 0) = pathDiag Z x A B := by
  unfold pairProd pathDiag
  rw [Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hstep : ∀ p : Fin 3, pathN Z x (A p) (B q) ^ (if p = q then 1 else 0)
      = if p = q then pathN Z x (A p) (B q) else 1 := by
    intro p; split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun p _ => hstep p),
    Finset.prod_ite_eq' univ q (fun p => pathN Z x (A p) (B q))]
  simp

/-- **The base `(2T, T)` product**: exponent `2T` on the matching, `T` off it. -/
theorem pairProd_base (T : ℕ) :
    pairProd Z x A B (fun p q => if p = q then 2 * T else T)
      = pathDiag Z x A B ^ (2 * T) * pathOff Z x A B ^ T := by
  have hsplit : (fun p q : Fin 3 => if p = q then 2 * T else T)
      = fun p q => T + T * (if p = q then 1 else 0) := by
    funext p q; split_ifs <;> ring
  rw [hsplit, pairProd_add, pairProd_const]
  have hpow : pairProd Z x A B (fun p q => T * (if p = q then 1 else 0))
      = pathDiag Z x A B ^ T := by
    rw [← pairProd_id_perm (Z := Z) (x := x) (A := A) (B := B)]
    unfold pairProd
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun pq _ => pow_mul' _ _ _
  rw [hpow, mul_pow]
  ring

theorem pairProd_off :
    pairProd Z x A B (fun p q => if p = q then 0 else 1) = pathOff Z x A B := by
  unfold pairProd
  rw [Fintype.prod_prod_type]
  have hstep : ∀ p q : Fin 3, pathN Z x (A p) (B q) ^ (if p = q then 0 else 1)
      = if p = q then 1 else pathN Z x (A p) (B q) := by
    intro p q; split_ifs <;> simp
  simp only [hstep]
  rw [pathOff_eq]
  simp only [Fin.prod_univ_three]
  simp

/-- **The repaired base `(2T - 2, T)`**, written with `T = S + 1` to stay in `ℕ`. -/
theorem pairProd_base_repaired (S : ℕ) :
    pairProd Z x A B (fun p q => if p = q then 2 * S else S + 1)
      = pathDiag Z x A B ^ (2 * S) * pathOff Z x A B ^ (S + 1) := by
  have hsplit : (fun p q : Fin 3 => if p = q then 2 * S else S + 1)
      = fun p q => (if p = q then 2 * S else S) + (if p = q then 0 else 1) := by
    funext p q; split_ifs <;> ring
  rw [hsplit, pairProd_add, pairProd_base, pairProd_off]
  ring

/-! ## Three-index bookkeeping on `Fin 3` -/

theorem prod_three_of_ne {M : Type*} [CommMonoid M] (f : Fin 3 → M) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ∏ p : Fin 3, f p = f i * f j * f k := by
  have hcard : ({i, j, k} : Finset (Fin 3)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
      Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
  have h : ({i, j, k} : Finset (Fin 3)) = univ := Finset.eq_univ_of_card _ (by simpa using hcard)
  rw [← h, Finset.prod_insert (by simp [hij, hik]), Finset.prod_insert (by simp [hjk]),
    Finset.prod_singleton, mul_assoc]

private theorem exists_third_index : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide

theorem fin3_eq_third (i j k c : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (h1 : c ≠ i) (h2 : c ≠ j) : c = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases c <;> simp_all

/-! ## The residual products of the §5.3 table -/

theorem resOrd_pairProd (σ : Equiv.Perm (Fin 3)) :
    pairProd Z x A B (fun p q => resOrd σ p q)
      = pathDiag Z x A B * ∏ q : Fin 3, pathN Z x (A (σ q)) (B q) := by
  have hr : (fun p q : Fin 3 => resOrd σ p q)
      = fun p q => (if p = q then 1 else 0) + (if p = σ q then 1 else 0) := by
    funext p q; simp [resOrd]
  rw [hr, pairProd_add, pairProd_id_perm, pairProd_perm]

theorem resClose_pairProd (σ : Equiv.Perm (Fin 3)) :
    pairProd Z x A B (fun p q => resClose σ p q)
      = (∏ q : Fin 3, pathN Z x (A (σ q)) (B q)) ^ 2 := by
  have hr : (fun p q : Fin 3 => resClose σ p q)
      = fun p q => 2 * (if p = σ q then 1 else 0) := by
    funext p q; simp [resClose]
  rw [hr, pairProd_two, pairProd_perm]

theorem resCloseRepaired_pairProd (σ : Equiv.Perm (Fin 3)) :
    pairProd Z x A B (fun p q => resCloseRepaired σ p q)
      = pairProd Z x A B (fun p q => resOrd σ p q) ^ 2 := by
  have hr : (fun p q : Fin 3 => resCloseRepaired σ p q)
      = fun p q => 2 * resOrd σ p q := by
    funext p q
    simp only [resCloseRepaired, resOrd, Matrix.of_apply]
    split_ifs <;> ring
  rw [hr]
  exact pairProd_two (fun p q => resOrd σ p q)

/-! ## Routing the generalized diagonal -/

/-- The `σ`-matching routes whenever `σ` has no 2-cycle: the reversed-pair obstruction of
`path_route` is exactly a transposed pair of `σ`. -/
theorem route_perm_of_no_two_cycle (h : IsPathPattern Z A B) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ c : Fin 3, σ (σ c) = c → σ c = c) (x : ℕ → ℕ) :
    ∏ z ∈ Z, x z ≤ ∏ q : Fin 3, pathN Z x (A (σ q)) (B q) := by
  refine path_route h.cardZ x (u := fun q => A (σ q)) (v := B)
    (h.injA.comp σ.injective) h.injB ?_
  rintro i j hij ⟨h1, h2, -, -⟩
  have hsj : σ j = i := h.extEq (σ j) i h1.symm
  have hsi : σ i = j := h.extEq (σ i) j h2.symm
  have hjj : σ (σ j) = j := by rw [hsj, hsi]
  exact hij ((hσ j hjj) ▸ hsj).symm

/-- **The ordinary residual inequality, uniform in the holonomy.**  When the `σ`-matching does
not route, `σ` transposes two indices whose two lists are aligned there, and the six single-colour
bounds of the seam configuration deliver the same product by hand. -/
theorem resOrd_bound (h : IsPathPattern Z A B) (σ : Equiv.Perm (Fin 3)) :
    (∏ z ∈ Z, x z) ^ 2 ≤ pairProd Z x A B (fun p q => resOrd σ p q) := by
  classical
  rw [resOrd_pairProd]
  have hid : ∏ z ∈ Z, x z ≤ pathDiag Z x A B := by
    rw [pathDiag_eq]; exact route_id h x
  by_cases hbad : ∃ i j : Fin 3, i ≠ j ∧ B i = A (σ j) ∧ B j = A (σ i) ∧
      A (σ i) ∈ Z ∧ A (σ j) ∈ Z
  · obtain ⟨i, j, hij, hb1, hb2, hm1, hm2⟩ := hbad
    have hsj : σ j = i := h.extEq (σ j) i hb1.symm
    have hsi : σ i = j := h.extEq (σ i) j hb2.symm
    rw [hsj] at hb1 hm2
    rw [hsi] at hb2 hm1
    -- `hb1 : B i = A i`, `hb2 : B j = A j`, `hm1 : A j ∈ Z`, `hm2 : A i ∈ Z`
    obtain ⟨k, hik, hjk⟩ := exists_third_index i j hij
    have hsk : σ k = k := by
      have h1 : σ k ≠ i := by
        rw [← hsj]; exact fun hh => hjk (σ.injective hh).symm
      have h2 : σ k ≠ j := by
        rw [← hsi]; exact fun hh => hik (σ.injective hh).symm
      exact fin3_eq_third i j k (σ k) hij hik hjk h1 h2
    have hne : A i ≠ A j := fun hh => hij (h.injA hh)
    -- the third colour of `Z`
    have hqmem : A j ∈ Z.erase (A i) := Finset.mem_erase.mpr ⟨Ne.symm hne, hm1⟩
    have hcard1 : ((Z.erase (A i)).erase (A j)).card = 1 := by
      rw [Finset.card_erase_of_mem hqmem, Finset.card_erase_of_mem hm2, h.cardZ]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
    have hwmem : w ∈ (Z.erase (A i)).erase (A j) := by rw [hw]; exact Finset.mem_singleton_self w
    have hwZ : w ∈ Z := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hwmem)
    have hwj : w ≠ A j := Finset.ne_of_mem_erase hwmem
    have hwi : w ≠ A i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hwmem)
    have hZeq : Z = insert (A i) (insert (A j) {w}) := by
      have e1 : Z.erase (A i) = insert (A j) {w} := by rw [← hw, Finset.insert_erase hqmem]
      rw [← Finset.insert_erase hm2, e1]
    have hXeq : ∏ z ∈ Z, x z = x (A i) * (x (A j) * x w) := by
      rw [hZeq, Finset.prod_insert (by simp [hne, Ne.symm hwi]),
        Finset.prod_insert (by simp [Ne.symm hwj]), Finset.prod_singleton]
    -- the six single-colour bounds
    have b1 : x (A j) ≤ pathN Z x (A i) (B i) := by
      rw [hb1]; exact single_le_pathN hm1 (Ne.symm hne) (Ne.symm hne)
    have b2 : x (A i) ≤ pathN Z x (A j) (B j) := by
      rw [hb2]; exact single_le_pathN hm2 hne hne
    have b3 : x w ≤ pathN Z x (A j) (B i) := by
      rw [hb1]; exact single_le_pathN hwZ hwj hwi
    have b4 : x w ≤ pathN Z x (A i) (B j) := by
      rw [hb2]; exact single_le_pathN hwZ hwi hwj
    have b5 : x (A i) ≤ pathN Z x (A k) (B k) :=
      single_le_pathN hm2 (fun hh => hik (h.injA hh)) (fun hh => hik (h.extEq i k hh))
    have b6 : x (A j) ≤ pathN Z x (A k) (B k) :=
      single_le_pathN hm1 (fun hh => hjk (h.injA hh)) (fun hh => hjk (h.extEq j k hh))
    unfold pathDiag
    rw [prod_three_of_ne (fun p => pathN Z x (A p) (B p)) i j k hij hik hjk,
      prod_three_of_ne (fun q => pathN Z x (A (σ q)) (B q)) i j k hij hik hjk]
    simp only [hsi, hsj, hsk]
    calc (∏ z ∈ Z, x z) ^ 2
        = x (A j) * x (A i) * (x w * x w) * (x (A i) * x (A j)) := by rw [hXeq]; ring
      _ ≤ pathN Z x (A i) (B i) * pathN Z x (A j) (B j) *
            (pathN Z x (A j) (B i) * pathN Z x (A i) (B j)) *
            (pathN Z x (A k) (B k) * pathN Z x (A k) (B k)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul b1 b2) (Nat.mul_le_mul b3 b4))
            (Nat.mul_le_mul b5 b6)
      _ = _ := by ring
  · push_neg at hbad
    have hm : ∏ z ∈ Z, x z ≤ ∏ q : Fin 3, pathN Z x (A (σ q)) (B q) := by
      refine path_route h.cardZ x (u := fun q => A (σ q)) (v := B)
        (h.injA.comp σ.injective) h.injB ?_
      rintro i j hij ⟨h1, h2, h3, h4⟩
      exact hbad i j hij h1 h2 h3 h4
    calc (∏ z ∈ Z, x z) ^ 2 = (∏ z ∈ Z, x z) * (∏ z ∈ Z, x z) := sq _
      _ ≤ _ := Nat.mul_le_mul hid hm

/-- The closing residual `2 P_{σ⁻¹}` against the naive base, available exactly when `σ` has no
2-cycle — the identity and the two three-cycles. -/
theorem resClose_bound (h : IsPathPattern Z A B) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ c : Fin 3, σ (σ c) = c → σ c = c) :
    (∏ z ∈ Z, x z) ^ 2 ≤ pairProd Z x A B (fun p q => resClose σ p q) := by
  rw [resClose_pairProd]
  have hm := route_perm_of_no_two_cycle h σ hσ x
  calc (∏ z ∈ Z, x z) ^ 2 ≤ (∏ q : Fin 3, pathN Z x (A (σ q)) (B q)) ^ 2 :=
        Nat.pow_le_pow_left hm 2
    _ = _ := rfl

/-- The repaired closing residual `2 P_{σ⁻¹} + 2 I`, available for **every** holonomy: it is
twice the ordinary residual. -/
theorem resCloseRepaired_bound (h : IsPathPattern Z A B) (σ : Equiv.Perm (Fin 3)) :
    (∏ z ∈ Z, x z) ^ 4 ≤ pairProd Z x A B (fun p q => resCloseRepaired σ p q) := by
  rw [resCloseRepaired_pairProd]
  calc (∏ z ∈ Z, x z) ^ 4 = ((∏ z ∈ Z, x z) ^ 2) ^ 2 := by ring
    _ ≤ _ := Nat.pow_le_pow_left (resOrd_bound h σ) 2

/-! ## The internal exponent step -/

/-- **The internal exponent step, base `(2T, T)`.**  Any exponent matrix that splits as the
base `(2T, T)` plus a residual satisfying the `d = 2` demand is discharged by `T` copies of the
interior cone point `(M,S) = (2,1)` and one application of the residual inequality; the total
exponent carried on each internal colour is `M + 2S + d = 4T + 2 = E`. -/
theorem internal_exponent_of_residual (h : IsPathPattern Z A B) (T : ℕ)
    (res : Fin 3 → Fin 3 → ℕ)
    (hres : (∏ z ∈ Z, x z) ^ 2 ≤ pairProd Z x A B res) :
    2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ pairProd Z x A B (fun p q => (if p = q then 2 * T else T) + res p q) := by
  rw [pairProd_add, pairProd_base]
  have hbase := path_cone_pow (D := pathDiag Z x A B) (O := pathOff Z x A B)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one h) (path_ray_off h) T 0
  calc 2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      = (2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2 * 0)) * (∏ z ∈ Z, x z) ^ 2 := by ring
    _ ≤ ((pathDiag Z x A B ^ 2 * pathOff Z x A B) ^ T * pathOff Z x A B ^ 0)
          * pairProd Z x A B res := Nat.mul_le_mul hbase hres
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- **The internal exponent step, repaired base `(2T - 2, T)`** with `T = S + 1`: `S` copies of
`(2,1)`, one copy of the off-matching ray `(0,1)`, and the `d = 4` repaired residual.  Total
exponent `2S + 2(S+1) + 4 = 4(S+1) + 2 = E`. -/
theorem internal_exponent_of_residual_repaired (h : IsPathPattern Z A B) (S : ℕ)
    (res : Fin 3 → Fin 3 → ℕ)
    (hres : (∏ z ∈ Z, x z) ^ 4 ≤ pairProd Z x A B res) :
    2 ^ (6 * S) * (∏ z ∈ Z, x z) ^ (4 * S + 6)
      ≤ pairProd Z x A B (fun p q => (if p = q then 2 * S else S + 1) + res p q) := by
  rw [pairProd_add, pairProd_base_repaired]
  have hbase := path_cone_pow (D := pathDiag Z x A B) (O := pathOff Z x A B)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one h) (path_ray_off h) S 1
  calc 2 ^ (6 * S) * (∏ z ∈ Z, x z) ^ (4 * S + 6)
      = (2 ^ (6 * S) * (∏ z ∈ Z, x z) ^ (4 * S + 2 * 1)) * (∏ z ∈ Z, x z) ^ 4 := by ring
    _ ≤ ((pathDiag Z x A B ^ 2 * pathOff Z x A B) ^ S * pathOff Z x A B ^ 1)
          * pairProd Z x A B res := Nat.mul_le_mul hbase hres
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- **Ordinary internal edge, every holonomy.** -/
theorem internal_exponent_ordinary_res (h : IsPathPattern Z A B) (σ : Equiv.Perm (Fin 3))
    (T : ℕ) :
    2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ pairProd Z x A B (fun p q => (if p = q then 2 * T else T) + resOrd σ p q) :=
  internal_exponent_of_residual h T _ (resOrd_bound h σ)

/-- **Closing internal edge, naive base, holonomy without a 2-cycle.** -/
theorem internal_exponent_closing_res (h : IsPathPattern Z A B) (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ c : Fin 3, σ (σ c) = c → σ c = c) (T : ℕ) :
    2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ pairProd Z x A B (fun p q => (if p = q then 2 * T else T) + resClose σ p q) :=
  internal_exponent_of_residual h T _ (resClose_bound h σ hσ)

/-- **Closing internal edge, repaired base, every holonomy.** -/
theorem internal_exponent_closing_repaired_res (h : IsPathPattern Z A B)
    (σ : Equiv.Perm (Fin 3)) (S : ℕ) :
    2 ^ (6 * S) * (∏ z ∈ Z, x z) ^ (4 * S + 6)
      ≤ pairProd Z x A B (fun p q => (if p = q then 2 * S else S + 1) + resCloseRepaired σ p q) :=
  internal_exponent_of_residual_repaired h S _ (resCloseRepaired_bound h σ)



end ListColoring

namespace ListColoring

open Finset RefTensor

variable {Z : Finset ℕ} {x : ℕ → ℕ} {A B : Fin 3 → ℕ}

/-- **The strict internal exponent step** (`§5.4` (5.11)): at an internal vertex whose two
terminal enumerations differ, the base `(2T, T)` block is paid at the strict rate
`729^T / 4^T = 2^{6T} C^T` instead of `2^{6T}`. -/
theorem internal_exponent_of_residual_strict (h : IsPathPattern Z A B) (hne : A ≠ B) (T : ℕ)
    (res : Fin 3 → Fin 3 → ℕ)
    (hres : (∏ z ∈ Z, x z) ^ 2 ≤ pairProd Z x A B res) :
    729 ^ T * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ 4 ^ T * pairProd Z x A B (fun p q => (if p = q then 2 * T else T) + res p q) := by
  rw [pairProd_add, pairProd_base]
  have hs := path_strict_cone h x hne T 0
  calc 729 ^ T * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      = (729 ^ T * (∏ z ∈ Z, x z) ^ (4 * T + 2 * 0)) * (∏ z ∈ Z, x z) ^ 2 := by ring
    _ ≤ (4 ^ T * ((pathDiag Z x A B ^ 2 * pathOff Z x A B) ^ T * pathOff Z x A B ^ 0))
          * pairProd Z x A B res := Nat.mul_le_mul hs hres
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-! ### The per-vertex bounds in the coordinates of `RefTensor.pair_exponent` -/

theorem pairProd_ordinary_eq {N : ℕ} (σ : Equiv.Perm (Fin 3)) (i : Fin (N + 1))
    (hi : i.val + 1 < N + 1) (Z : Finset ℕ) (x : ℕ → ℕ) (A B : Fin 3 → ℕ) :
    (∏ pr : Fin 3 × Fin 3, pathN Z x (A pr.1) (B pr.2) ^
        (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = pr), Uw σ a))
      = pairProd Z x A B
          (fun p q => (if p = q then 2 * gammaPlus N else gammaPlus N) + resOrd σ p q) := by
  unfold pairProd
  refine Finset.prod_congr rfl fun pr _ => ?_
  congr 1
  exact pairMarginal_ordinary σ i hi pr.1 pr.2

theorem vertex_ordinary {N : ℕ} (σ : Equiv.Perm (Fin 3)) (i : Fin (N + 1))
    (hi : i.val + 1 < N + 1) (h : IsPathPattern Z A B) :
    2 ^ (6 * gammaPlus N) * (∏ z ∈ Z, x z) ^ (4 * gammaPlus N + 2)
      ≤ ∏ pr : Fin 3 × Fin 3, pathN Z x (A pr.1) (B pr.2) ^
          (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = pr), Uw σ a) := by
  rw [pairProd_ordinary_eq σ i hi]
  exact internal_exponent_of_residual h _ _ (resOrd_bound h σ)

theorem vertex_ordinary_strict {N : ℕ} (σ : Equiv.Perm (Fin 3)) (i : Fin (N + 1))
    (hi : i.val + 1 < N + 1) (h : IsPathPattern Z A B) (hne : A ≠ B) :
    729 ^ gammaPlus N * (∏ z ∈ Z, x z) ^ (4 * gammaPlus N + 2)
      ≤ 4 ^ gammaPlus N * ∏ pr : Fin 3 × Fin 3, pathN Z x (A pr.1) (B pr.2) ^
          (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = pr), Uw σ a) := by
  rw [pairProd_ordinary_eq σ i hi]
  exact internal_exponent_of_residual_strict h hne _ _ (resOrd_bound h σ)

/-- **The `σ`-twist of the seam**: reindexing the second colour by `σ`. -/
theorem prod_align (σ : Equiv.Perm (Fin 3)) (f : Fin 3 → Fin 3 → ℕ) (D : Fin 3 → Fin 3 → ℕ) :
    (∏ pq : Fin 3 × Fin 3, f pq.1 pq.2 ^ D pq.1 pq.2)
      = ∏ pq : Fin 3 × Fin 3, f pq.1 (σ pq.2) ^ D pq.1 (σ pq.2) := by
  rw [← Equiv.prod_comp ((Equiv.refl (Fin 3)).prodCongr σ)
    (fun pq : Fin 3 × Fin 3 => f pq.1 pq.2 ^ D pq.1 pq.2)]
  rfl

theorem pairProd_closing_eq {N : ℕ} (σ : Equiv.Perm (Fin 3))
    (Z : Finset ℕ) (x : ℕ → ℕ) (A B : Fin 3 → ℕ) :
    (∏ pr : Fin 3 × Fin 3, pathN Z x (A pr.1) (B pr.2) ^
        (∑ a ∈ univ.filter
          (fun a : Fin (N + 1) → Fin 3 =>
            (a (Fin.last N), a (Fin.last N + 1)) = pr), Uw σ a))
      = pairProd Z x A (fun q => B (σ q))
          (fun p q => (if p = q then 2 * gammaPlus N else gammaPlus N) + resClose σ p q) := by
  have hz : (Fin.last N : Fin (N + 1)) + 1 = 0 := by apply Fin.ext; simp
  rw [hz]
  rw [prod_align σ (fun p q => pathN Z x (A p) (B q))
    (fun p q => ∑ a ∈ univ.filter
      (fun a : Fin (N + 1) → Fin 3 => (a (Fin.last N), a 0) = (p, q)), Uw σ a)]
  unfold pairProd
  refine Finset.prod_congr rfl fun pr _ => ?_
  congr 1
  exact pairMarginal_closing σ pr.1 pr.2

/-- Three-cycle seam: the naive base `(2T, T)` survives. -/
theorem vertex_closing_noTwoCycle {N : ℕ} (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ c : Fin 3, σ (σ c) = c → σ c = c)
    (h : IsPathPattern Z A (fun q => B (σ q))) :
    2 ^ (6 * gammaPlus N) * (∏ z ∈ Z, x z) ^ (4 * gammaPlus N + 2)
      ≤ ∏ pr : Fin 3 × Fin 3, pathN Z x (A pr.1) (B pr.2) ^
          (∑ a ∈ univ.filter
            (fun a : Fin (N + 1) → Fin 3 =>
              (a (Fin.last N), a (Fin.last N + 1)) = pr), Uw σ a) := by
  rw [pairProd_closing_eq σ]
  exact internal_exponent_of_residual h _ _ (resClose_bound h σ hσ)

/-- Transposition seam: the base must be repaired to `(2T-2, T)`, at a cost of `2^6`. -/
theorem vertex_closing_repaired {N : ℕ} (hN : 1 ≤ N) (σ : Equiv.Perm (Fin 3))
    (h : IsPathPattern Z A (fun q => B (σ q))) :
    2 ^ (6 * (gammaPlus N - 1)) * (∏ z ∈ Z, x z) ^ (4 * gammaPlus N + 2)
      ≤ ∏ pr : Fin 3 × Fin 3, pathN Z x (A pr.1) (B pr.2) ^
          (∑ a ∈ univ.filter
            (fun a : Fin (N + 1) → Fin 3 =>
              (a (Fin.last N), a (Fin.last N + 1)) = pr), Uw σ a) := by
  have hT : 1 ≤ gammaPlus N := one_le_gammaPlus hN
  obtain ⟨S, hS⟩ : ∃ S, gammaPlus N = S + 1 := ⟨gammaPlus N - 1, by omega⟩
  rw [pairProd_closing_eq σ]
  have hsplit : (fun p q : Fin 3 =>
        (if p = q then 2 * gammaPlus N else gammaPlus N) + resClose σ p q)
      = fun p q => (if p = q then 2 * S else S + 1) + resCloseRepaired σ p q := by
    funext p q
    rw [hS]
    simp only [resClose, resCloseRepaired, Matrix.of_apply]
    split_ifs <;> omega
  rw [hsplit]
  have hb := internal_exponent_of_residual_repaired (Z := Z) (x := x) (A := A)
    (B := fun q => B (σ q)) h S _ (resCloseRepaired_bound h σ)
  have he : 4 * S + 6 = 4 * gammaPlus N + 2 := by rw [hS]; ring
  rw [he] at hb
  have he2 : gammaPlus N - 1 = S := by omega
  rw [he2]
  exact hb

end ListColoring

namespace ListColoring

open Finset SimpleGraph RefTensor

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A nontrivial holonomy forces an **ordinary** internal vertex with unequal terminal
enumerations: if every ordinary step were constant the seam bijection would be the identity. -/
theorem exists_unequal_ordinary {M : ℕ} (σ : Fin (M + 1) → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hinj : Function.Injective (σ 0))
    (hclose : ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = P x) (hP : P ≠ 1) :
    ∃ (i : Fin (M + 1)) (h : i.val + 1 < M + 1), σ ⟨i.val + 1, h⟩ ≠ σ i := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ k : ℕ, ∀ hk : k < M + 1, σ ⟨k, hk⟩ = σ 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < M + 1 := by omega
      have hstep := hcon ⟨k, hk'⟩ (by simpa using hk)
      calc σ ⟨k + 1, hk⟩ = σ ⟨(⟨k, hk'⟩ : Fin (M + 1)).val + 1, by simpa using hk⟩ := rfl
        _ = σ ⟨k, hk'⟩ := hstep
        _ = σ 0 := ih hk'
  have hlast : σ (Fin.last M) = σ 0 := hall M (by omega)
  refine hP (Equiv.ext fun q => ?_)
  have := hclose q q (by rw [hlast])
  simpa using this.symm

/-- The word weight of the terminal-cycle model. -/
noncomputable def wordWeight {M : ℕ} (jx : CycIx M ≃ V) (L : ListAssignment V) (w : V → ℕ → ℕ)
    (σ : Fin (M + 1) → Fin 3 → ℕ) (g : Fin (M + 1) → Fin 3) : ℕ :=
  (∏ i, w (tv jx i) (σ i (g i))) *
    ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1)))

/-- Two-point product formula. -/
theorem prod_two_points {α : Type*} [Fintype α] [DecidableEq α] (i j : α) (hij : i ≠ j)
    (u v : ℕ) :
    (∏ k : α, (if k = i then u else if k = j then v else 1)) = u * v := by
  classical
  have hrw : ∀ k : α, (if k = i then u else if k = j then v else 1)
      = (if k = i then u else 1) * (if k = j then v else 1) := by
    intro k
    by_cases h1 : k = i
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hij, mul_one]
    · rw [if_neg h1, if_neg h1, one_mul]
  rw [Finset.prod_congr rfl (fun k _ => hrw k), Finset.prod_mul_distrib,
    Finset.prod_ite_eq' univ i (fun _ => u), Finset.prod_ite_eq' univ j (fun _ => v),
    if_pos (Finset.mem_univ i), if_pos (Finset.mem_univ j)]

theorem prod_single_point {M : ℕ} (i₀ : Fin (M + 1)) (u v : ℕ) :
    (∏ k : Fin (M + 1), (if k = i₀ then u else v)) = u * v ^ M := by
  classical
  rw [← Finset.mul_prod_erase univ (fun k => if k = i₀ then u else v) (Finset.mem_univ i₀),
    if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk)),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
    Fintype.card_fin]
  simp

end ListColoring

namespace ListColoring

open Finset SimpleGraph RefTensor

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The master mass-weighted bound at a non-identity holonomy** (handoff (5.19)).  `K` is the
seam slack (`1` for a three-cycle seam, `2^6` for a repaired transposition seam) and `hbudget`
is the §5.5 comparison: the entropy denominator against `M` ordinary blocks `2^{6T}`, one strict
block `729^T/4^T` at the unequal vertex `i₀`, and the seam slack. -/
theorem master_bound_nonidentity {M : ℕ} (hM : 1 ≤ M) (jx : CycIx M ≃ V)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c)
    (σ : Fin (M + 1) → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (i₀ : Fin (M + 1)) (hi₀ : i₀.val + 1 < M + 1) (hne : σ i₀ ≠ σ (i₀ + 1))
    (K : ℕ) (hK : 0 < K)
    (hseam : 2 ^ (6 * gammaPlus M) *
        (∏ z ∈ L (iv jx (Fin.last M)), w (iv jx (Fin.last M)) z) ^ (4 * gammaPlus M + 2)
      ≤ K * ∏ pr : Fin 3 × Fin 3,
          pathN (L (iv jx (Fin.last M))) (w (iv jx (Fin.last M)))
            (σ (Fin.last M) pr.1) (σ (Fin.last M + 1) pr.2) ^
            (∑ a ∈ univ.filter
              (fun a : Fin (M + 1) → Fin 3 =>
                (a (Fin.last M), a (Fin.last M + 1)) = pr), Uw P a))
    (hbudget : (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) * (4 ^ gammaPlus M * K)
      ≤ 729 ^ gammaPlus M * (2 ^ (6 * gammaPlus M)) ^ M) :
    (∏ v, W v) ^ (3 * (4 * gammaPlus M + 2)) * ∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a
      ≤ ∏ g : Fin (M + 1) → Fin 3, wordWeight jx L w σ g ^ Uw P g := by
  classical
  set T := gammaPlus M with hT
  set E := 4 * gammaPlus M + 2 with hE
  have hlast : i₀ ≠ Fin.last M := by
    intro hh
    rw [hh] at hi₀
    simp only [Fin.val_last] at hi₀
    omega
  -- split the word weight
  have hsplit : (∏ g : Fin (M + 1) → Fin 3, wordWeight jx L w σ g ^ Uw P g)
      = (∏ g : Fin (M + 1) → Fin 3, (∏ i, w (tv jx i) (σ i (g i))) ^ Uw P g) *
        (∏ g : Fin (M + 1) → Fin 3,
          (∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
            ^ Uw P g) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => mul_pow _ _ _
  rw [hsplit, terminal_exponent P (fun i c => w (tv jx i) (σ i c)),
    pair_exponent P (fun i p q => pathN (L (iv jx i)) (w (iv jx i)) (σ i p) (σ (i + 1) q))]
  -- the terminal half
  have hterm : (∏ i : Fin (M + 1), W (tv jx i)) ^ (3 * E)
      ≤ ∏ i : Fin (M + 1), ∏ c : Fin 3, w (tv jx i) (σ i c) ^ E := by
    rw [← Finset.prod_pow]
    refine Finset.prod_le_prod' fun i _ => ?_
    have h1 : ∏ c ∈ L (tv jx i), w (tv jx i) c = ∏ c : Fin 3, w (tv jx i) (σ i c) :=
      prod_list_eq_prod_index (hL _) (hmem i) (hinj i) _
    calc W (tv jx i) ^ (3 * E) = (W (tv jx i) ^ 3) ^ E := by rw [← pow_mul]
      _ ≤ (∏ c ∈ L (tv jx i), w (tv jx i) c) ^ E := Nat.pow_le_pow_left (hdom _) _
      _ = (∏ c : Fin 3, w (tv jx i) (σ i c)) ^ E := by rw [h1]
      _ = ∏ c : Fin 3, w (tv jx i) (σ i c) ^ E := (Finset.prod_pow _ _ _).symm
  -- the internal half
  set Q : Fin (M + 1) → ℕ := fun i => ∏ pr : Fin 3 × Fin 3,
      pathN (L (iv jx i)) (w (iv jx i)) (σ i pr.1) (σ (i + 1) pr.2) ^
        (∑ a ∈ univ.filter
          (fun a : Fin (M + 1) → Fin 3 => (a i, a (i + 1)) = pr), Uw P a) with hQ
  set Y : Fin (M + 1) → ℕ := fun i => ∏ z ∈ L (iv jx i), w (iv jx i) z with hY
  have hvert : ∀ i : Fin (M + 1),
      (if i = i₀ then 729 ^ T else 2 ^ (6 * T)) * Y i ^ E
        ≤ (if i = i₀ then 4 ^ T else if i = Fin.last M then K else 1) * Q i := by
    intro i
    by_cases hii : i = i₀
    · subst hii
      rw [if_pos rfl, if_pos rfl]
      exact vertex_ordinary_strict (x := w (iv jx i)) P i hi₀
        (isPathPattern_ordinary jx L hL σ hmem hinj hchain i hi₀) hne
    · by_cases hil : i = Fin.last M
      · subst hil
        rw [if_neg hii, if_neg hii, if_pos rfl]
        exact hseam
      · have hi : i.val + 1 < M + 1 := by
          have h1 : i.val ≤ M := by omega
          have h2 : i.val ≠ M := fun hh => hil (Fin.ext hh)
          omega
        rw [if_neg hii, if_neg hii, if_neg hil, one_mul]
        exact vertex_ordinary (x := w (iv jx i)) P i hi
          (isPathPattern_ordinary jx L hL σ hmem hinj hchain i hi)
  have hmul := Finset.prod_le_prod' (s := (univ : Finset (Fin (M + 1)))) (fun i _ => hvert i)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_single_point i₀ (729 ^ T) (2 ^ (6 * T)),
    prod_two_points i₀ (Fin.last M) hlast (4 ^ T) K, Finset.prod_pow] at hmul
  -- combine with the budget
  have hYW : (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * E) ≤ (∏ i : Fin (M + 1), Y i) ^ E := by
    rw [pow_mul, ← Finset.prod_pow]
    exact Nat.pow_le_pow_left (Finset.prod_le_prod' fun i _ => hdom _) E
  have hint : (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * E) *
        (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) ≤ ∏ i : Fin (M + 1), Q i := by
    have hpos : 0 < 4 ^ T * K := Nat.mul_pos (pow_pos (by norm_num : (0:ℕ) < 4) T) hK
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * E) *
          (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) * (4 ^ T * K)
        = ((∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) * (4 ^ T * K)) *
            (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * E) := by ring
      _ ≤ (729 ^ T * (2 ^ (6 * T)) ^ M) * (∏ i : Fin (M + 1), Y i) ^ E :=
          Nat.mul_le_mul hbudget hYW
      _ ≤ (4 ^ T * K) * ∏ i : Fin (M + 1), Q i := hmul
      _ = (∏ i : Fin (M + 1), Q i) * (4 ^ T * K) := by ring
  -- assemble
  have hWsplit : (∏ v, W v) = (∏ i : Fin (M + 1), W (tv jx i)) *
      (∏ i : Fin (M + 1), W (iv jx i)) := by
    rw [← Equiv.prod_comp jx (fun v => W v), Fintype.prod_sum_type]
    rfl
  rw [hWsplit, mul_pow]
  calc (∏ i : Fin (M + 1), W (tv jx i)) ^ (3 * E) *
        (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * E) *
        (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a)
      = (∏ i : Fin (M + 1), W (tv jx i)) ^ (3 * E) *
          ((∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * E) *
            (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a)) := by ring
    _ ≤ (∏ i : Fin (M + 1), ∏ c : Fin 3, w (tv jx i) (σ i c) ^ E) * ∏ i : Fin (M + 1), Q i :=
        Nat.mul_le_mul hterm hint

end ListColoring

namespace ListColoring

open Finset SimpleGraph RefTensor

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The even-cycle tensor capacity at a non-identity holonomy.** -/
theorem cycle_core_nonidentity {M : ℕ} (hM : 1 ≤ M) (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c)
    (σ : Fin (M + 1) → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (i₀ : Fin (M + 1)) (hi₀ : i₀.val + 1 < M + 1) (hne : σ i₀ ≠ σ (i₀ + 1))
    (K : ℕ) (hK : 0 < K)
    (hseam : 2 ^ (6 * gammaPlus M) *
        (∏ z ∈ L (iv jx (Fin.last M)), w (iv jx (Fin.last M)) z) ^ (4 * gammaPlus M + 2)
      ≤ K * ∏ pr : Fin 3 × Fin 3,
          pathN (L (iv jx (Fin.last M))) (w (iv jx (Fin.last M)))
            (σ (Fin.last M) pr.1) (σ (Fin.last M + 1) pr.2) ^
            (∑ a ∈ univ.filter
              (fun a : Fin (M + 1) → Fin 3 =>
                (a (Fin.last M), a (Fin.last M + 1)) = pr), Uw P a))
    (hbudget : (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) * (4 ^ gammaPlus M * K)
      ≤ 729 ^ gammaPlus M * (2 ^ (6 * gammaPlus M)) ^ M) :
    ((4 * gammaPlus M + 2) * ∏ v, W v) ^ 3
      ≤ ∏ c ∈ L (tv jx 0), rootedWcol G L w (tv jx 0) c := by
  classical
  set E : ℕ := 4 * gammaPlus M + 2 with hEdef
  have hEpos : 0 < E := by rw [hEdef]; omega
  have hR : ∀ c : Fin 3, rootedWcol G L w (tv jx 0) (σ 0 c)
      = ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter (fun g => g 0 = c),
          wordWeight jx L w σ g :=
    fun c => rootedWcol_eq_sum_index jx hadj L hL w σ hmem hinj c
  have hprod : ∏ c ∈ L (tv jx 0), rootedWcol G L w (tv jx 0) c
      = ∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter
          (fun g => g 0 = c), wordWeight jx L w σ g := by
    rw [prod_list_eq_prod_index (hL _) (hmem 0) (hinj 0)
      (fun c => rootedWcol G L w (tv jx 0) c)]
    exact Finset.prod_congr rfl fun c _ => hR c
  have hfib := fibre_amgm_even P (wordWeight jx L w σ)
  have hmaster := master_bound_nonidentity hM jx L hL w W hdom σ P hmem hinj hchain
    i₀ hi₀ hne K hK hseam hbudget
  have hUpos : 0 < ∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a :=
    Finset.prod_pos fun a _ => Nat.pow_pos (Uw_pos _ a)
  have hchainA : ((E * ∏ v, W v) ^ 3) ^ E *
        (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a)
      ≤ (∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter
            (fun g => g 0 = c), wordWeight jx L w σ g) ^ E *
        (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) := by
    calc ((E * ∏ v, W v) ^ 3) ^ E * (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a)
        = E ^ (3 * E) *
            ((∏ v, W v) ^ (3 * E) * ∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) := by
          rw [← pow_mul, mul_pow]; ring
      _ ≤ E ^ (3 * E) * ∏ g : Fin (M + 1) → Fin 3, wordWeight jx L w σ g ^ Uw P g :=
          Nat.mul_le_mul_left _ hmaster
      _ ≤ _ := hfib
  have hcancel : ((E * ∏ v, W v) ^ 3) ^ E
      ≤ (∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter
          (fun g => g 0 = c), wordWeight jx L w σ g) ^ E :=
    Nat.le_of_mul_le_mul_right hchainA hUpos
  rw [hprod]
  exact (Nat.pow_le_pow_iff_left (by omega : E ≠ 0)).mp hcancel

end ListColoring

/-! ## §5.6 — the two budget comparisons, the seam, and the branch -/

namespace ListColoring

open Finset RefTensor

/-- The dichotomy of a nontrivial permutation of three points: either it has no fixed point
(a three-cycle, and then it has no 2-cycle either), or it has exactly one (a transposition). -/
theorem fin3_fun_dichotomy : ∀ f : Fin 3 → Fin 3, Function.Injective f → (∃ c, f c ≠ c) →
    (((univ.filter fun c : Fin 3 => f c = c).card = 0 ∧ ∀ c, f (f c) = c → f c = c)
      ∨ (univ.filter fun c : Fin 3 => f c = c).card = 1) := by decide

/-- `P ≠ 1` in the form the dichotomy consumes. -/
theorem exists_moved_of_ne_one {P : Equiv.Perm (Fin 3)} (hP : P ≠ 1) : ∃ c, P c ≠ c := by
  by_contra hc
  push_neg at hc
  exact hP (Equiv.ext fun c => by simpa using hc c)

/-- **The three-cycle budget** (`f = 0`, seam slack `K = 1`). -/
theorem budget_threeCycle {M : ℕ} (hM : 3 ≤ M) (P : Equiv.Perm (Fin 3))
    (hf : fixCount P = 0) :
    (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) * (4 ^ gammaPlus M * 1)
      ≤ 729 ^ gammaPlus M * (2 ^ (6 * gammaPlus M)) ^ M := by
  have hk : (movedConst (N := M) P).card = 3 := by
    have := card_movedConst_add_fixCount (N := M) P; omega
  have hgen := prod_Uw_pow_Uw_gen (N := M) P
  rw [hk, hf] at hgen
  set q := 2 ^ M with hq
  set T := gammaPlus M with hT
  set U := ∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a with hU
  have hent := entropy_three_cycle_bound M hM
  have hqq : q ^ (3 * q) = 2 ^ (3 * (q * M)) := by
    rw [hq, ← pow_mul]; congr 1; ring
  have hcube : ((q + 1) ^ (q + 1)) ^ 3 = (q + 1) ^ (3 * (q + 1)) := by
    rw [← pow_mul]; congr 1; ring
  have hpos : 0 < 2 ^ (3 * (q * M)) * 64 ^ T := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc U * (4 ^ T * 1) * (2 ^ (3 * (q * M)) * 64 ^ T)
      = (U * 2 ^ (3 * (q * M))) * (4 * 64 : ℕ) ^ T := by rw [mul_pow]; ring
    _ = ((q + 1) ^ (3 * (q + 1)) * 256 ^ T) * 2 ^ ((M + 1) * (6 * T + 2 * 0)) := by
        rw [hgen, hcube]; norm_num; ring
    _ ≤ (q ^ (3 * q) * 729 ^ T) * 2 ^ ((M + 1) * (6 * T + 2 * 0)) :=
        Nat.mul_le_mul_right _ hent
    _ = 729 ^ T * (2 ^ (6 * T)) ^ M * (2 ^ (3 * (q * M)) * 64 ^ T) := by
        rw [hqq, ← pow_mul]
        rw [show (M + 1) * (6 * T + 2 * 0) = 6 * T * M + 6 * T by ring]
        rw [pow_add]
        rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]
        ring

/-- **The transposition budget** (`f = 1`, seam slack `K = 2^6`). -/
theorem budget_transposition {M : ℕ} (hM : 3 ≤ M) (P : Equiv.Perm (Fin 3))
    (hf : fixCount P = 1) :
    (∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a) * (4 ^ gammaPlus M * 64)
      ≤ 729 ^ gammaPlus M * (2 ^ (6 * gammaPlus M)) ^ M := by
  have hk : (movedConst (N := M) P).card = 2 := by
    have := card_movedConst_add_fixCount (N := M) P; omega
  have hgen := prod_Uw_pow_Uw_gen (N := M) P
  rw [hk, hf] at hgen
  set q := 2 ^ M with hq
  set T := gammaPlus M with hT
  set U := ∏ a : Fin (M + 1) → Fin 3, Uw P a ^ Uw P a with hU
  have hent := entropy_transposition_bound M hM
  have hqq : q ^ (2 * q) = 2 ^ (2 * (q * M)) := by
    rw [hq, ← pow_mul]; congr 1; ring
  have hsq : ((q + 1) ^ (q + 1)) ^ 2 = (q + 1) ^ (2 * (q + 1)) := by
    rw [← pow_mul]; congr 1; ring
  have h64 : (64 : ℕ) * 2 ^ (2 * M + 2) = 2 ^ (2 * M + 8) := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; ring
  have hpos : 0 < 2 ^ (2 * (q * M)) * 64 ^ T * 2 ^ (2 * M + 2) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc U * (4 ^ T * 64) * (2 ^ (2 * (q * M)) * 64 ^ T * 2 ^ (2 * M + 2))
      = (U * 2 ^ (2 * (q * M))) * (4 * 64 : ℕ) ^ T * (64 * 2 ^ (2 * M + 2)) := by
        rw [mul_pow]; ring
    _ = ((q + 1) ^ (2 * (q + 1)) * 2 ^ (2 * M + 8) * 256 ^ T) *
          2 ^ ((M + 1) * (6 * T + 2 * 1)) := by
        rw [hgen, hsq, h64]; norm_num; ring
    _ ≤ (q ^ (2 * q) * 729 ^ T) * 2 ^ ((M + 1) * (6 * T + 2 * 1)) :=
        Nat.mul_le_mul_right _ hent
    _ = 729 ^ T * (2 ^ (6 * T)) ^ M * (2 ^ (2 * (q * M)) * 64 ^ T * 2 ^ (2 * M + 2)) := by
        rw [hqq, ← pow_mul]
        rw [show (M + 1) * (6 * T + 2 * 1) = 6 * T * M + (6 * T + (2 * M + 2)) by ring]
        rw [pow_add, pow_add]
        rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]
        ring

end ListColoring

namespace ListColoring

open Finset SimpleGraph RefTensor

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The even-cycle tensor capacity at a non-identity holonomy, `M ≥ 3`**: the seam and the
budget of `cycle_core_nonidentity` discharged from the §5.3 residual table and the §5.5 scalar
comparisons.  Both holonomy types are covered: a three-cycle seam takes the naive `(2T,T)` base
with slack `K = 1`, a transposition seam the repaired `(2T-2,T)` base with slack `K = 2^6`. -/
theorem cycle_core_nonidentity_large {M : ℕ} (hM : 3 ≤ M) (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c)
    (σ : Fin (M + 1) → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (hclose : ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = P x) (hP : P ≠ 1) :
    ((4 * gammaPlus M + 2) * ∏ v, W v) ^ 3
      ≤ ∏ c ∈ L (tv jx 0), rootedWcol G L w (tv jx 0) c := by
  classical
  -- the strict internal vertex
  obtain ⟨i₀, hi₀, hne0⟩ := exists_unequal_ordinary σ P (hinj 0) hclose hP
  have hsucc : i₀ + 1 = (⟨i₀.val + 1, hi₀⟩ : Fin (M + 1)) := by
    apply Fin.ext
    rw [Fin.val_add_one_of_lt (by exact Fin.lt_def.mpr (by simpa using by omega))]
  have hne : σ i₀ ≠ σ (i₀ + 1) := by rw [hsucc]; exact fun h => hne0 h.symm
  -- the closing path pattern
  have hz : (Fin.last M : Fin (M + 1)) + 1 = 0 := by apply Fin.ext; simp
  have hpp : IsPathPattern (L (iv jx (Fin.last M))) (σ (Fin.last M))
      (fun q => σ (Fin.last M + 1) (P q)) := by
    rw [hz]; exact isPathPattern_closing jx L hL σ P hinj hclose
  have hT : 1 ≤ gammaPlus M := one_le_gammaPlus (by omega)
  -- the holonomy dichotomy
  rcases fin3_fun_dichotomy (⇑P) P.injective (exists_moved_of_ne_one hP) with ⟨hf, htwo⟩ | hf
  · -- three-cycle seam: naive base, `K = 1`
    refine cycle_core_nonidentity (by omega) jx hadj L hL w W hdom σ P hmem hinj hchain
      i₀ hi₀ hne 1 one_pos ?_ (budget_threeCycle hM P hf)
    rw [one_mul]
    exact vertex_closing_noTwoCycle (N := M) (Z := L (iv jx (Fin.last M)))
      (x := w (iv jx (Fin.last M))) (A := σ (Fin.last M)) (B := σ (Fin.last M + 1)) P htwo hpp
  · -- transposition seam: repaired base, `K = 2^6`
    refine cycle_core_nonidentity (by omega) jx hadj L hL w W hdom σ P hmem hinj hchain
      i₀ hi₀ hne 64 (by norm_num) ?_ (budget_transposition hM P hf)
    have hrep := vertex_closing_repaired (N := M) (Z := L (iv jx (Fin.last M)))
      (x := w (iv jx (Fin.last M))) (A := σ (Fin.last M)) (B := σ (Fin.last M + 1))
      (by omega : 1 ≤ M) P hpp
    calc 2 ^ (6 * gammaPlus M) *
          (∏ z ∈ L (iv jx (Fin.last M)), w (iv jx (Fin.last M)) z) ^ (4 * gammaPlus M + 2)
        = 64 * (2 ^ (6 * (gammaPlus M - 1)) *
            (∏ z ∈ L (iv jx (Fin.last M)), w (iv jx (Fin.last M)) z) ^
              (4 * gammaPlus M + 2)) := by
          rw [show 6 * gammaPlus M = 6 * (gammaPlus M - 1) + 6 by omega, pow_add]
          norm_num; ring
      _ ≤ 64 * _ := Nat.mul_le_mul_left _ hrep

/-- **`EvenCycleBranchLarge` — the general `m ≥ 7` branch of `cycle_gm_bound_even`.** -/
theorem branch_large : EvenCycleBranchLarge V G := by
  intro m hm ix hadj hpar L hL w W hdom
  rw [Nat.even_iff] at hpar
  obtain ⟨M, rfl⟩ : ∃ M, m = 2 * M + 1 := ⟨m / 2, by omega⟩
  have hM3 : 3 ≤ M := by omega
  obtain ⟨jx, hjx, hroot⟩ := exists_cyc_model (M := M) ix hadj
  obtain ⟨σ, P, hmem, hinj, hchain, hclose⟩ := exists_terminal_closing_model jx L hL
  by_cases hP : P = 1
  · subst hP
    exact cycle_gm_bound_even_identity (M := M) (by omega) ix hadj L hL w W hdom jx hjx hroot σ
      hmem hinj hchain (fun x y h => by simpa using hclose x y h)
  · have hA : rootedCol G (constList V 3) (ix 0) 0 = 4 * gammaPlus M + 2 := by
      rw [rootedCol_constList_cycle (by omega) ix hadj,
        show 2 * M + 1 + 1 = 2 * M + 2 from rfl, uniformA_three_even]
    rw [hA, ← hroot]
    exact cycle_core_nonidentity_large hM3 jx hjx L hL w W hdom σ P hmem hinj hchain hclose hP

end ListColoring

#print axioms ListColoring.budget_threeCycle
#print axioms ListColoring.budget_transposition
#print axioms ListColoring.cycle_core_nonidentity
#print axioms ListColoring.cycle_core_nonidentity_large
#print axioms ListColoring.branch_large

/-! Non-vacuity: the normalizer the branch clears at `m = 7` (`C₈`) is `86`, not `0`. -/
#guard (ListColoring.uniformA 3 8 == 86) && (4 * ListColoring.gammaPlus 3 + 2 == 86)
