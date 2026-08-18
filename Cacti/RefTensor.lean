/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Tensor
import Cacti.Induction

open Finset

namespace ListColoring
namespace RefTensor

open Matrix

/-! ## §5.2 reference tensor over `M = N + 1` positions and three colours. -/

/-- `γ_{a+b} = 3 γ_a γ_b + γ_a + γ_b`. -/
theorem gammaPlus_add (a b : ℕ) :
    gammaPlus (a + b) = 3 * gammaPlus a * gammaPlus b + gammaPlus a + gammaPlus b := by
  have ha := three_mul_gammaPlus_add_one a
  have hb := three_mul_gammaPlus_add_one b
  have hab := three_mul_gammaPlus_add_one (a + b)
  have h : (4:ℕ) ^ (a + b) = 4 ^ a * 4 ^ b := pow_add 4 a b
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 3 by norm_num) ?_
  nlinarith [ha, hb, hab, h]

theorem prod_ite_two_one {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ∏ i ∈ s, (if p i then 2 else 1) = 2 ^ (s.filter p).card := by
  simp [Finset.prod_ite]

/-- Splitting a word of length `n + 2` into its first letter and its tail. -/
def consEq (n : ℕ) : Fin 3 × (Fin (n + 1) → Fin 3) ≃ (Fin (n + 2) → Fin 3) where
  toFun p := Fin.cons p.1 p.2
  invFun a := (a 0, Fin.tail a)
  left_inv p := by simp
  right_inv a := by simp

@[simp] theorem consEq_apply (n : ℕ) (c : Fin 3) (b : Fin (n + 1) → Fin 3) :
    consEq n (c, b) = Fin.cons c b := rfl

/-! ### The path weight and its transfer-matrix evaluation -/

/-- The product of the ordinary-edge weights of a word: `∏_{i<N} (J+I)(a_i, a_{i+1})`. -/
def pathWeight {N : ℕ} (a : Fin (N + 1) → Fin 3) : ℕ :=
  ∏ i : Fin N, onesPlus (a i.castSucc) (a i.succ)

theorem pathWeight_cons {N : ℕ} (c : Fin 3) (b : Fin (N + 1) → Fin 3) :
    pathWeight (Fin.cons c b) = onesPlus c (b 0) * pathWeight b := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
  congr 1

/-- **The transfer-matrix evaluation of the path sum.**  For any boundary weight `g`,
`∑_a (∏ ordinary edges) · g(a_0, a_N) = ∑_{i,j} ((J+I)^N)_{ij} g(i,j)`. -/
theorem sum_pathWeight : ∀ (N : ℕ) (g : Fin 3 → Fin 3 → ℕ),
    ∑ a : Fin (N + 1) → Fin 3, pathWeight a * g (a 0) (a (Fin.last N))
      = ∑ i : Fin 3, ∑ j : Fin 3, (onesPlus ^ N) i j * g i j := by
  intro N
  induction N with
  | zero =>
    intro g
    rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 3)).symm
      (fun a => pathWeight a * g (a 0) (a (Fin.last 0)))]
    simp [pathWeight, Matrix.one_apply, Fin.sum_univ_three]
  | succ N ih =>
    intro g
    rw [← Equiv.sum_comp (consEq N)
      (fun a => pathWeight a * g (a 0) (a (Fin.last (N + 1))))]
    rw [Fintype.sum_prod_type]
    have step : ∀ c : Fin 3,
        (∑ b : Fin (N + 1) → Fin 3,
            pathWeight (consEq N (c, b)) *
              g (consEq N (c, b) 0) (consEq N (c, b) (Fin.last (N + 1))))
          = ∑ i : Fin 3, ∑ j : Fin 3, (onesPlus ^ N) i j * (onesPlus c i * g c j) := by
      intro c
      rw [← ih (fun x y => onesPlus c x * g c y)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [consEq_apply, pathWeight_cons, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ]
      ring
    rw [Finset.sum_congr rfl (fun c _ => step c)]
    rw [pow_succ' onesPlus N]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    ring

/-- The `p = 0` case of the pinned sum. -/
theorem sum_pathWeight_pin_zero (N : ℕ) (c : Fin 3) (g : Fin 3 → Fin 3 → ℕ) :
    ∑ a : Fin (N + 1) → Fin 3,
        pathWeight a * (if a 0 = c then g (a 0) (a (Fin.last N)) else 0)
      = ∑ j : Fin 3, (onesPlus ^ N) c j * g c j := by
  rw [sum_pathWeight N (fun x y => if x = c then g x y else 0)]
  fin_cases c <;> simp [Fin.sum_univ_three]

/-- The pinned path sum: with the word forced to take the value `c` at position `p`, the
transfer product splits at `p` into `(J+I)^p` and `(J+I)^{N-p}`. -/
theorem sum_pathWeight_pin : ∀ (N : ℕ) (p : Fin (N + 1)) (c : Fin 3) (g : Fin 3 → Fin 3 → ℕ),
    ∑ a : Fin (N + 1) → Fin 3,
        pathWeight a * (if a p = c then g (a 0) (a (Fin.last N)) else 0)
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (onesPlus ^ (p : ℕ)) i c * ((onesPlus ^ (N - (p : ℕ))) c j * g i j) := by
  intro N
  induction N with
  | zero =>
    intro p c g
    refine Fin.cases ?_ (fun q => q.elim0) p
    rw [sum_pathWeight_pin_zero 0 c g]
    simp only [Fin.val_zero, pow_zero, Nat.sub_zero, Matrix.one_apply]
    fin_cases c <;> simp
  | succ N ih =>
    intro p c g
    refine Fin.cases ?_ ?_ p
    · rw [sum_pathWeight_pin_zero (N + 1) c g]
      simp only [Fin.val_zero, pow_zero, Nat.sub_zero, Matrix.one_apply]
      fin_cases c <;> simp [Fin.sum_univ_three]
    · intro q
      rw [← Equiv.sum_comp (consEq N)
        (fun a => pathWeight a * (if a q.succ = c then g (a 0) (a (Fin.last (N + 1))) else 0))]
      rw [Fintype.sum_prod_type]
      have step : ∀ c₀ : Fin 3,
          (∑ b : Fin (N + 1) → Fin 3,
              pathWeight (consEq N (c₀, b)) *
                (if consEq N (c₀, b) q.succ = c then
                  g (consEq N (c₀, b) 0) (consEq N (c₀, b) (Fin.last (N + 1)))
                 else 0))
            = ∑ i : Fin 3, ∑ j : Fin 3,
                (onesPlus ^ (q : ℕ)) i c *
                  ((onesPlus ^ (N - (q : ℕ))) c j * (onesPlus c₀ i * g c₀ j)) := by
        intro c₀
        rw [← ih q c (fun x y => onesPlus c₀ x * g c₀ y)]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [consEq_apply, pathWeight_cons, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ,
          Fin.cons_succ]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun c₀ _ => step c₀)]
      have hval : ((q.succ : Fin (N + 2)) : ℕ) = (q : ℕ) + 1 := rfl
      rw [hval]
      have hsub : N + 1 - ((q : ℕ) + 1) = N - (q : ℕ) := by omega
      rw [hsub, pow_succ' onesPlus (q : ℕ)]
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      ring

/-! ### `h` and `U` -/

/-- `f = fix σ`. -/
def fixCount (σ : Equiv.Perm (Fin 3)) : ℕ := (univ.filter fun c : Fin 3 => σ c = c).card

/-- `h(a)` of handoff (5.3): the number of matching edges the word obeys — the `N` ordinary
edges carry the identity matching, the closing edge `N → 0` carries the holonomy `σ`. -/
def hw {N : ℕ} (σ : Equiv.Perm (Fin 3)) (a : Fin (N + 1) → Fin 3) : ℕ :=
  (univ.filter fun i : Fin N => a i.castSucc = a i.succ).card
    + (if a 0 = σ (a (Fin.last N)) then 1 else 0)

/-- `h(a)` in the wrap-around presentation of handoff (5.3): a single filter over all `M`
cyclic edges, using `Fin.last N + 1 = 0`. -/
def hwCyc {N : ℕ} (σ : Equiv.Perm (Fin 3)) (a : Fin (N + 1) → Fin 3) : ℕ :=
  (univ.filter fun i : Fin (N + 1) =>
      a (i + 1) = (if i = Fin.last N then σ (a i) else a i)).card

/-- The two presentations of `h` agree. -/
theorem hwCyc_eq_hw {N : ℕ} (σ : Equiv.Perm (Fin 3)) (a : Fin (N + 1) → Fin 3) :
    hwCyc σ a = hw σ a := by
  unfold hwCyc hw
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : (j.castSucc : Fin (N + 1)) < Fin.last N := Fin.castSucc_lt_last j
    have hne : (j.castSucc : Fin (N + 1)) ≠ Fin.last N := ne_of_lt hlt
    have hadd : (j.castSucc : Fin (N + 1)) + 1 = j.succ := by
      apply Fin.ext
      rw [Fin.val_add_one_of_lt hlt]
      simp
    rw [if_neg hne, hadd]
    by_cases h : a j.castSucc = a j.succ
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  · rw [if_pos rfl]
    have hz : (Fin.last N : Fin (N + 1)) + 1 = 0 := by
      apply Fin.ext; simp
    rw [hz]

/-- `U(a)` of handoff (5.3): `2 ^ h(a)`, plus one on each constant word that `σ` moves. -/
def Uw {N : ℕ} (σ : Equiv.Perm (Fin 3)) (a : Fin (N + 1) → Fin 3) : ℕ :=
  2 ^ hw σ a + (if (∀ i, a i = a 0) ∧ σ (a 0) ≠ a 0 then 1 else 0)

/-- `2 ^ h(a)` factors as the ordinary transfer product times the closing weight. -/
theorem two_pow_hw {N : ℕ} (σ : Equiv.Perm (Fin 3)) (a : Fin (N + 1) → Fin 3) :
    2 ^ hw σ a = pathWeight a * (if a 0 = σ (a (Fin.last N)) then 2 else 1) := by
  unfold hw pathWeight
  rw [pow_add]
  congr 1
  · rw [← prod_ite_two_one]
    exact Finset.prod_congr rfl fun i _ => by rw [onesPlus_apply]
  · by_cases h : a 0 = σ (a (Fin.last N)) <;> simp [h]

/-! ### The pinned sums -/

private theorem sum_three (A : ℕ) (c t : Fin 3) :
    ∑ i : Fin 3, ((if i = c then A + 1 else A) * (if i = t then 2 else 1))
      = 4 * A + 1 + (if t = c then 1 else 0) := by
  fin_cases c <;> fin_cases t <;> simp [Fin.sum_univ_three] <;> omega

private theorem sum_perm_eq (σ : Equiv.Perm (Fin 3)) (c : Fin 3) :
    ∑ j : Fin 3, (if σ j = c then 1 else 0) = 1 := by
  have h := Equiv.sum_comp σ (fun x : Fin 3 => if x = c then (1:ℕ) else 0)
  rw [h]
  fin_cases c <;> simp

/-- **The pinned `2 ^ h` marginal.**  For every position `p` and colour `c`,
`∑_{a : a_p = c} 2^{h(a)} = 4 γ_N + 1 + [σ c = c]`. -/
theorem marginal_two_pow_hw {N : ℕ} (σ : Equiv.Perm (Fin 3)) (p : Fin (N + 1)) (c : Fin 3) :
    (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a p = c), 2 ^ hw σ a)
      = 4 * gammaPlus N + 1 + (if σ c = c then 1 else 0) := by
  have hfilter :
      (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a p = c), 2 ^ hw σ a)
        = ∑ a : Fin (N + 1) → Fin 3,
            pathWeight a *
              (if a p = c then (if a 0 = σ (a (Fin.last N)) then 2 else 1) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a p = c
    · simp only [h, if_true]; exact two_pow_hw σ a
    · simp [h]
  rw [hfilter]
  rw [sum_pathWeight_pin N p c (fun i j => if i = σ j then 2 else 1)]
  set s := (p : ℕ) with hs_def
  set t := N - s with ht_def
  have hst : s + t = N := by
    have hlt : s < N + 1 := p.isLt
    omega
  set A := gammaPlus s with hA_def
  set B := gammaPlus t with hB_def
  have hA : ∀ i : Fin 3, (onesPlus ^ s) i c = if i = c then A + 1 else A := by
    intro i; rw [onesPlus_pow_apply]
  have hB : ∀ j : Fin 3, (onesPlus ^ t) c j = if c = j then B + 1 else B := by
    intro j; rw [onesPlus_pow_apply]
  simp only [hA, hB]
  rw [Finset.sum_comm]
  have inner : ∀ j : Fin 3,
      (∑ i : Fin 3, (if i = c then A + 1 else A) *
          ((if c = j then B + 1 else B) * (if i = σ j then 2 else 1)))
        = (B * (4 * A + 1)) + B * (if σ j = c then 1 else 0)
            + (if c = j then 4 * A + 1 else 0)
            + (if c = j then (if σ j = c then 1 else 0) else 0) := by
    intro j
    have h1 : (∑ i : Fin 3, (if i = c then A + 1 else A) *
        ((if c = j then B + 1 else B) * (if i = σ j then 2 else 1)))
        = (if c = j then B + 1 else B) *
            ∑ i : Fin 3, ((if i = c then A + 1 else A) * (if i = σ j then 2 else 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, sum_three A c (σ j)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => inner j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : (∑ _j : Fin 3, B * (4 * A + 1)) = 3 * (B * (4 * A + 1)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have e2 : (∑ j : Fin 3, B * (if σ j = c then 1 else 0)) = B := by
    rw [← Finset.mul_sum, sum_perm_eq σ c, mul_one]
  have e3 : (∑ j : Fin 3, (if c = j then 4 * A + 1 else 0)) = 4 * A + 1 := by
    fin_cases c <;> simp
  have e4 : (∑ j : Fin 3, (if c = j then (if σ j = c then 1 else 0) else 0))
      = if σ c = c then 1 else 0 := by
    fin_cases c <;> simp
  rw [e1, e2, e3, e4]
  have hgam : gammaPlus N = 3 * A * B + A + B := by
    rw [← hst, hA_def, hB_def]; exact gammaPlus_add s t
  rw [hgam]
  ring

/-- The pinned correction count: only the constant word `c` can contribute, and it does exactly
when `σ` moves `c`. -/
theorem marginal_corr {N : ℕ} (σ : Equiv.Perm (Fin 3)) (p : Fin (N + 1)) (c : Fin 3) :
    (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a p = c),
        (if (∀ i, a i = a 0) ∧ σ (a 0) ≠ a 0 then 1 else 0))
      = if σ c = c then 0 else 1 := by
  rw [← Finset.card_filter]
  by_cases hc : σ c = c
  · rw [if_pos hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a ha ⟨hconst, hne⟩
    rw [Finset.mem_filter] at ha
    have h0 : a 0 = c := by rw [← hconst p]; exact ha.2
    exact hne (by rw [h0, hc])
  · rw [if_neg hc]
    have hset : (univ.filter (fun a : Fin (N + 1) → Fin 3 => a p = c)).filter
        (fun a => (∀ i, a i = a 0) ∧ σ (a 0) ≠ a 0) = {fun _ => c} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hconst, hne⟩
        have h0 : a 0 = c := by rw [← hconst p]; exact hp
        funext i; rw [hconst i, h0]
      · rintro rfl
        exact ⟨rfl, fun i => rfl, hc⟩
    rw [hset, Finset.card_singleton]

/-! ### The two headline statements -/

/-- **Every one-coordinate marginal of `U` is exactly `E = 4T + 2 = P/3`**, for every position
`p`, every colour `c` and every holonomy `σ` (handoff (5.2)). -/
theorem marginal_Uw {N : ℕ} (σ : Equiv.Perm (Fin 3)) (p : Fin (N + 1)) (c : Fin 3) :
    (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a p = c), Uw σ a)
      = 4 * gammaPlus N + 2 := by
  unfold Uw
  rw [Finset.sum_add_distrib, marginal_two_pow_hw, marginal_corr]
  by_cases hc : σ c = c <;> simp [hc]

/-- **The total mass `∑_a U(a) = P = 12 T + 6`**, uniformly in the holonomy `σ`. -/
theorem sum_Uw_eq_twelve_T (N : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ∑ a : Fin (N + 1) → Fin 3, Uw σ a = 12 * gammaPlus N + 6 := by
  rw [← Finset.sum_fiberwise (univ : Finset (Fin (N + 1) → Fin 3)) (fun a => a 0) (Uw σ)]
  rw [Finset.sum_congr rfl (fun c _ => marginal_Uw σ (0 : Fin (N + 1)) c)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- **The total mass `∑_a U(a) = P = 4^M + 2`** (handoff (5.2)/(5.4)). -/
theorem sum_Uw (N : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ∑ a : Fin (N + 1) → Fin 3, Uw σ a = 4 ^ (N + 1) + 2 := by
  rw [sum_Uw_eq_twelve_T, umP_eq_twelve_mul_gammaPlus]

/-- Division-free form of "the marginal is `P / 3`" (handoff (5.2)). -/
theorem three_mul_marginal_Uw {N : ℕ} (σ : Equiv.Perm (Fin 3)) (p : Fin (N + 1)) (c : Fin 3) :
    3 * (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a p = c), Uw σ a)
      = 4 ^ (N + 1) + 2 := by
  rw [marginal_Uw, three_mul_umE]

/-! ### The bare `2 ^ h` layer: (5.4) -/

/-- The closing transfer matrix `B = J + P_σ` (the `z = 2` companion of `onesPlus = J + I`). -/
def closeMat (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => if j = σ i then 2 else 1

theorem closeMat_apply (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    closeMat σ i j = if j = σ i then 2 else 1 := rfl

/-- **The transfer-matrix form of (5.4)**: `∑_a 2^{h(a)} = tr((J+I)^{M-1} · B)`. -/
theorem sum_two_pow_hw_eq_trace (N : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ∑ a : Fin (N + 1) → Fin 3, 2 ^ hw σ a
      = ∑ i : Fin 3, ∑ j : Fin 3, (onesPlus ^ N) i j * closeMat σ j i := by
  rw [Finset.sum_congr rfl (fun a _ => two_pow_hw σ a)]
  exact sum_pathWeight N (fun i j => closeMat σ j i)

theorem fixCount_eq_sum (σ : Equiv.Perm (Fin 3)) :
    fixCount σ = ∑ c : Fin 3, (if σ c = c then 1 else 0) := Finset.card_filter _ _

/-- **(5.4) at `z = 2`**, subtraction-free in `ℕ`: `∑_a 2^{h(a)} = 4^M + f - 1`. -/
theorem sum_two_pow_hw (N : ℕ) (σ : Equiv.Perm (Fin 3)) :
    (∑ a : Fin (N + 1) → Fin 3, 2 ^ hw σ a) + 1 = 4 ^ (N + 1) + fixCount σ := by
  have hf :
      (∑ a : Fin (N + 1) → Fin 3, 2 ^ hw σ a) = 3 * (4 * gammaPlus N + 1) + fixCount σ := by
    rw [← Finset.sum_fiberwise (univ : Finset (Fin (N + 1) → Fin 3)) (fun a => a 0)
      (fun a => 2 ^ hw σ a)]
    rw [Finset.sum_congr rfl (fun c _ => marginal_two_pow_hw σ (0 : Fin (N + 1)) c)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← fixCount_eq_sum]
  have hg := three_mul_gammaPlus_add_one N
  rw [hf, pow_succ]
  omega

end RefTensor

open RefTensor

/-- The reference masses are positive. -/
theorem Uw_pos {N : ℕ} (σ : Equiv.Perm (Fin 3)) (a : Fin (N + 1) → Fin 3) : 0 < Uw σ a := by
  unfold Uw
  have : 0 < 2 ^ hw σ a := Nat.pow_pos (by omega)
  omega

/-- **The three-fibre AM–GM of §5.6**: splitting the words by their root colour and applying
(5.18) on each fibre — where the reference masses sum to the marginal `E = 4γ_N + 2` — bounds the
mass-weighted product of the word weights by the product of the three fibre sums. -/
theorem fibre_amgm_even {N : ℕ} (σ : Equiv.Perm (Fin 3)) (X : (Fin (N + 1) → Fin 3) → ℕ) :
    (4 * gammaPlus N + 2) ^ (3 * (4 * gammaPlus N + 2)) *
        ∏ a : Fin (N + 1) → Fin 3, X a ^ Uw σ a
      ≤ (∏ c : Fin 3, ∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c), X a)
          ^ (4 * gammaPlus N + 2)
        * ∏ a : Fin (N + 1) → Fin 3, (Uw σ a) ^ (Uw σ a) := by
  classical
  set E : ℕ := 4 * gammaPlus N + 2 with hE
  have hEpos : 0 < E := by omega
  -- (5.18) on each fibre
  have hfib : ∀ c : Fin 3,
      E ^ E * ∏ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c), X a ^ Uw σ a
        ≤ (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c), X a) ^ E
          * ∏ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c), (Uw σ a) ^ (Uw σ a) := by
    intro c
    exact weighted_amgm_masses _ X (Uw σ) hEpos (marginal_Uw σ 0 c) (fun a _ => Uw_pos σ a)
  -- multiply the three fibres and refold the products
  have hmul := Finset.prod_le_prod' (s := (univ : Finset (Fin 3))) (fun c _ => hfib c)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Finset.prod_mul_distrib] at hmul
  have hXfib : ∏ c : Fin 3, ∏ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c),
      X a ^ Uw σ a = ∏ a : Fin (N + 1) → Fin 3, X a ^ Uw σ a :=
    Finset.prod_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (a 0)) _
  have hUfib : ∏ c : Fin 3, ∏ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c),
      (Uw σ a) ^ (Uw σ a) = ∏ a : Fin (N + 1) → Fin 3, (Uw σ a) ^ (Uw σ a) :=
    Finset.prod_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (a 0)) _
  have hpowfib : ∏ c : Fin 3,
      (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c), X a) ^ E
      = (∏ c : Fin 3, ∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a 0 = c), X a) ^ E :=
    Finset.prod_pow _ _ _
  rw [hXfib, hUfib, hpowfib] at hmul
  rw [Nat.mul_comm 3 E]
  exact hmul


/-- **The terminal exponent bookkeeping of §5.6**: because every one-coordinate marginal of the
reference masses is exactly `E = 4γ_N + 2`, the terminal weights enter the mass-weighted product
with that one exponent at every terminal and every colour. -/
theorem terminal_exponent {N : ℕ} (σ : Equiv.Perm (Fin 3)) (y : Fin (N + 1) → Fin 3 → ℕ) :
    ∏ a : Fin (N + 1) → Fin 3, (∏ i, y i (a i)) ^ Uw σ a
      = ∏ i : Fin (N + 1), ∏ c : Fin 3, (y i c) ^ (4 * gammaPlus N + 2) := by
  classical
  have hstep : ∀ i : Fin (N + 1),
      ∏ a : Fin (N + 1) → Fin 3, (y i (a i)) ^ Uw σ a
        = ∏ c : Fin 3, (y i c) ^ (4 * gammaPlus N + 2) := by
    intro i
    rw [← Finset.prod_fiberwise_of_maps_to (g := fun a : Fin (N + 1) → Fin 3 => a i)
      (t := (univ : Finset (Fin 3))) (fun a _ => Finset.mem_univ (a i))
      (fun a => (y i (a i)) ^ Uw σ a)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2] :
      ∀ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => a i = c),
        (y i (a i)) ^ Uw σ a = (y i c) ^ Uw σ a)]
    rw [Finset.prod_pow_eq_pow_sum, marginal_Uw σ i c]
  calc ∏ a : Fin (N + 1) → Fin 3, (∏ i, y i (a i)) ^ Uw σ a
      = ∏ a : Fin (N + 1) → Fin 3, ∏ i, (y i (a i)) ^ Uw σ a := by
        exact Finset.prod_congr rfl fun a _ => (Finset.prod_pow _ _ _).symm
    _ = ∏ i : Fin (N + 1), ∏ a : Fin (N + 1) → Fin 3, (y i (a i)) ^ Uw σ a := Finset.prod_comm
    _ = ∏ i : Fin (N + 1), ∏ c : Fin 3, (y i c) ^ (4 * gammaPlus N + 2) :=
        Finset.prod_congr rfl fun i _ => hstep i


/-- **The pair-marginal exponent bookkeeping of §5.3/§5.6**: the internal `pathN` factors enter
the mass-weighted product through the PAIR marginals of the reference masses — which is exactly
what the residual table of §5.3 computes. The terminal half is `terminal_exponent`. -/
theorem pair_exponent {N : ℕ} (σ : Equiv.Perm (Fin 3)) (z : Fin (N + 1) → Fin 3 → Fin 3 → ℕ) :
    ∏ a : Fin (N + 1) → Fin 3, (∏ i, z i (a i) (a (i + 1))) ^ Uw σ a
      = ∏ i : Fin (N + 1), ∏ p : Fin 3 × Fin 3, (z i p.1 p.2) ^
          (∑ a ∈ univ.filter
            (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = p), Uw σ a) := by
  classical
  have hstep : ∀ i : Fin (N + 1),
      ∏ a : Fin (N + 1) → Fin 3, (z i (a i) (a (i + 1))) ^ Uw σ a
        = ∏ p : Fin 3 × Fin 3, (z i p.1 p.2) ^
            (∑ a ∈ univ.filter
              (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = p), Uw σ a) := by
    intro i
    rw [← Finset.prod_fiberwise_of_maps_to
      (g := fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)))
      (t := (univ : Finset (Fin 3 × Fin 3))) (fun a _ => Finset.mem_univ _)
      (fun a => (z i (a i) (a (i + 1))) ^ Uw σ a)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Finset.prod_congr rfl (fun a ha => by
      have h := (Finset.mem_filter.mp ha).2
      rw [show a i = p.1 from congrArg Prod.fst h, show a (i + 1) = p.2 from congrArg Prod.snd h] :
      ∀ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = p),
        (z i (a i) (a (i + 1))) ^ Uw σ a = (z i p.1 p.2) ^ Uw σ a)]
    rw [Finset.prod_pow_eq_pow_sum]
  calc ∏ a : Fin (N + 1) → Fin 3, (∏ i, z i (a i) (a (i + 1))) ^ Uw σ a
      = ∏ a : Fin (N + 1) → Fin 3, ∏ i, (z i (a i) (a (i + 1))) ^ Uw σ a :=
        Finset.prod_congr rfl fun a _ => (Finset.prod_pow _ _ _).symm
    _ = ∏ i : Fin (N + 1), ∏ a : Fin (N + 1) → Fin 3, (z i (a i) (a (i + 1))) ^ Uw σ a :=
        Finset.prod_comm
    _ = _ := Finset.prod_congr rfl fun i _ => hstep i

end ListColoring

/-! ## Sanity evaluations against the intended combinatorics. -/
section
open ListColoring ListColoring.RefTensor Finset

private def sAll : List (Equiv.Perm (Fin 3)) :=
  [1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
   Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1]

-- fix counts: identity 3, three transpositions 1, two three-cycles 0
#guard sAll.map fixCount == [3, 1, 1, 1, 0, 0]

-- total mass P = 4^M + 2, uniformly in σ, for M = 2..5
#guard [1,2,3,4].all fun N => sAll.all fun σ =>
  ((∑ a : Fin (N+1) → Fin 3, Uw σ a) == 4 ^ (N+1) + 2)

-- every one-coordinate marginal is E = 4T + 2, for M = 2..5
#guard [1,2,3,4].all fun N => sAll.all fun σ =>
  (List.finRange (N+1)).all fun p => [0,1,2].all fun c =>
    ((∑ a ∈ univ.filter (fun a : Fin (N+1) → Fin 3 => a p = c), Uw σ a)
      == 4 * gammaPlus N + 2)

-- the bare 2^h tensor misses: its marginals are 85, not the required E = 4·γ₃ + 2 = 86.  The
-- `+1` correction in `Uw` is load-bearing.
#guard (List.finRange 4).all fun p =>
  (∑ a ∈ univ.filter (fun a : Fin 4 → Fin 3 => a p = 0), 2 ^ hw (Equiv.swap 0 1) a) == 85

#guard [1,2,3,4].all fun N => sAll.all fun σ =>
  ((∑ a : Fin (N+1) → Fin 3, 2 ^ hw σ a) + 1 == 4 ^ (N+1) + fixCount σ)

-- the trace form of (5.4)
#guard [1,2,3,4].all fun N => sAll.all fun σ =>
  ((∑ a : Fin (N+1) → Fin 3, 2 ^ hw σ a)
    == ∑ i : Fin 3, ∑ j : Fin 3, (onesPlus ^ N) i j * closeMat σ j i)

-- the wrap-around presentation of `h` agrees with the split one
#guard [1,2,3].all fun N => sAll.all fun σ =>
  decide (∀ a : Fin (N+1) → Fin 3, hwCyc σ a = hw σ a)

end

#print axioms ListColoring.RefTensor.sum_Uw
#print axioms ListColoring.RefTensor.marginal_Uw
#print axioms ListColoring.RefTensor.three_mul_marginal_Uw
#print axioms ListColoring.RefTensor.sum_two_pow_hw
#print axioms ListColoring.RefTensor.sum_pathWeight_pin
