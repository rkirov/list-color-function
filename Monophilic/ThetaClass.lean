/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.RubinHard

/-!
# Draft: chains along an arm
-/

open Finset

namespace Monophilic

open SimpleGraph

/-! ### Alternating chains -/

/-- **The alternating chain.** -/
theorem alt_chain {p q : ℕ} (g : ℕ → ℕ) (k m : ℕ)
    (hmem : ∀ j, k ≤ j → j < m → g j = p ∨ g j = q)
    (hne : ∀ j, j + 1 < m → g j ≠ g (j + 1)) (h0 : g k = q) :
    ∀ i, k + i < m → g (k + i) = if i % 2 = 0 then q else p := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
      intro hlt
      have hgi := ih (by omega)
      have hstep := hne (k + i) (by omega)
      have hmem' := hmem (k + i + 1) (by omega) (by omega)
      rw [show k + (i + 1) = k + i + 1 from by omega]
      by_cases hpar : i % 2 = 0
      · rw [if_pos hpar] at hgi
        rw [if_neg (by omega : ¬ ((i + 1) % 2 = 0))]
        rcases hmem' with h | h
        · exact h
        · exact absurd (hgi.trans h.symm) hstep
      · rw [if_neg hpar] at hgi
        rw [if_pos (by omega : (i + 1) % 2 = 0)]
        rcases hmem' with h | h
        · exact absurd (hgi.trans h.symm) hstep
        · exact h

/-- **Constant lists alternate.** -/
theorem const_chain (g : ℕ → ℕ) {m : ℕ}
    (hg : ∀ j, j < m → g j = 1 ∨ g j = 2)
    (hne : ∀ j, j + 1 < m → g j ≠ g (j + 1)) :
    ∀ i, i < m → g i = if i % 2 = 0 then g 0 else 3 - g 0 := by
  intro i hi
  have h := alt_chain (p := 3 - g 0) (q := g 0) g 0 m
    (fun j _ hj => by have := hg j hj; have := hg 0 (by omega); omega) hne rfl i (by omega)
  simpa using h

/-- **The forced chain along a blocking arm.** -/
theorem armBlockLists_forced (α β : ℕ) {m : ℕ} (hm : 2 ≤ m) (g : ℕ → ℕ)
    (hg : ∀ j, j < m → g j ∈ armBlockLists α β m j)
    (hne : ∀ j, j + 1 < m → g j ≠ g (j + 1)) (h0 : g 0 ≠ α) :
    g (m - 1) = β := by
  have hg0 : g 0 = 3 := by
    have h := hg 0 (by omega)
    rw [show armBlockLists α β m 0 = ({α, 3} : Finset ℕ) from by simp [armBlockLists]] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    tauto
  by_cases hpar : m % 2 = 0
  · have hmem : ∀ j, 0 ≤ j → j < m → g j = β ∨ g j = 3 := by
      intro j _ hj
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · exact Or.inr hg0
      · have h := hg j hj
        rw [show armBlockLists α β m j = ({3, β} : Finset ℕ) from by
          simp only [armBlockLists, if_pos hpar, if_neg (by omega : ¬ (j = 0))]] at h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        tauto
    have h := alt_chain (p := β) (q := 3) g 0 m hmem hne hg0 (m - 1) (by omega)
    rw [if_neg (by omega : ¬ ((m - 1) % 2 = 0))] at h
    simpa using h
  · have hg1 : g 1 = 4 := by
      have h := hg 1 (by omega)
      rw [show armBlockLists α β m 1 = ({3, 4} : Finset ℕ) from by
        simp only [armBlockLists, if_neg hpar, if_neg (by omega : ¬ ((1 : ℕ) = 0)),
          if_true]] at h
      have hs : g 0 ≠ g 1 := by simpa using hne 0 (by omega)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rw [hg0] at hs
      tauto
    have hg2 : g 2 = β := by
      have h := hg 2 (by omega)
      rw [show armBlockLists α β m 2 = ({4, β} : Finset ℕ) from by
        simp only [armBlockLists, if_neg hpar, if_neg (by omega : ¬ ((2 : ℕ) = 0)),
          if_neg (by omega : ¬ ((2 : ℕ) = 1)), if_true]] at h
      have hs : g 1 ≠ g 2 := by simpa using hne 1 (by omega)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rw [hg1] at hs
      tauto
    have hmem : ∀ j, 2 ≤ j → j < m → g j = 3 ∨ g j = β := by
      intro j hj2 hj
      rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · rw [show j = 2 from by omega]
        exact Or.inr hg2
      · have h := hg j hj
        rw [show armBlockLists α β m j = ({3, β} : Finset ℕ) from by
          simp only [armBlockLists, if_neg hpar, if_neg (by omega : ¬ (j = 0)),
            if_neg (by omega : ¬ (j = 1)), if_neg (by omega : ¬ (j = 2))]] at h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        tauto
    have h := alt_chain (p := 3) (q := β) g 2 m hmem hne hg2 (m - 3) (by omega)
    rw [if_pos (by omega : (m - 3) % 2 = 0), show 2 + (m - 3) = m - 1 from by omega] at h
    exact h

/-! ### What an arm blocks -/

/-- **An arm with constant lists `{1, 2}` blocks exactly one of the two diagonals.** -/
theorem const_block {m α β : ℕ} (g : ℕ → ℕ)
    (hg : ∀ j, j < m → g j = 1 ∨ g j = 2)
    (hne : ∀ j, j + 1 < m → g j ≠ g (j + 1))
    (h0 : 1 ≤ m → g 0 ≠ α) (h1 : 1 ≤ m → g (m - 1) ≠ β)
    (hd : m = 0 → α ≠ β) (hα : α = 1 ∨ α = 2) (hβ : β = 1 ∨ β = 2) :
    (α = β ↔ m % 2 = 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := hd rfl
    omega
  · have hchain := const_chain g hg hne (m - 1) (by omega)
    have e0 := hg 0 (by omega)
    have e1 := hg (m - 1) (by omega)
    have hh0 := h0 hm
    have hh1 := h1 hm
    by_cases hpar : (m - 1) % 2 = 0
    · rw [if_pos hpar] at hchain; omega
    · rw [if_neg hpar] at hchain; omega

/-! ### Reading off the arms of `thetaGen` -/

/-- The first vertex of an arm with at least one interior vertex is joined to the first branch
vertex. -/
private lemma armStepB_head (o m ps pt : ℕ) (hm : m ≠ 0) : armStepB o m ps pt ps o = true := by
  simp only [armStepB, if_neg hm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  exact Or.inl (Or.inl ⟨trivial, trivial⟩)

/-- Consecutive interior vertices of an arm are joined. -/
private lemma armStepB_mid (o m ps pt j : ℕ) (hj : j + 1 < m) :
    armStepB o m ps pt (o + j) (o + j + 1) = true := by
  simp only [armStepB, if_neg (show ¬ (m = 0) from by omega), Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, and_true]
  omega

/-- The last vertex of an arm with at least one interior vertex is joined to the second branch
vertex. -/
private lemma armStepB_last (o m ps pt : ℕ) (hm : m ≠ 0) :
    armStepB o m ps pt (o + (m - 1)) pt = true := by
  simp only [armStepB, if_neg hm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, and_true]
  omega

/-- An arm with no interior vertex is the single edge joining the two branch vertices. -/
private lemma armStepB_direct (o ps pt : ℕ) : armStepB o 0 ps pt ps pt = true := by
  simp [armStepB]

/-- The first arm of `θ_{a,b,c}` sits inside its adjacency. -/
private lemma thetaGenAdjB_arm1 (a b c x y : ℕ)
    (h : armStepB 0 (a - 1) (a + b + c - 3) (a + b + c - 2) x y = true) :
    thetaGenAdjB a b c x y = true := by simp [thetaGenAdjB, h]

/-- The second arm of `θ_{a,b,c}` sits inside its adjacency. -/
private lemma thetaGenAdjB_arm2 (a b c x y : ℕ)
    (h : armStepB (a - 1) (b - 1) (a + b + c - 3) (a + b + c - 2) x y = true) :
    thetaGenAdjB a b c x y = true := by simp [thetaGenAdjB, h]

/-- The third arm of `θ_{a,b,c}` sits inside its adjacency. -/
private lemma thetaGenAdjB_arm3 (a b c x y : ℕ)
    (h : armStepB (a + b - 2) (c - 1) (a + b + c - 3) (a + b + c - 2) x y = true) :
    thetaGenAdjB a b c x y = true := by simp [thetaGenAdjB, h]

/-- **The four constraints an arm imposes on a coloring**, read on indices. -/
private lemma arm_facts {a b c : ℕ} (hsum : 5 ≤ a + b + c) (F : ℕ → ℕ)
    (hadj : ∀ i j, i < a + b + c - 1 → j < a + b + c - 1 → i ≠ j →
      thetaGenAdjB a b c i j = true → F i ≠ F j)
    (o m : ℕ) (harm : ∀ x y, armStepB o m (a + b + c - 3) (a + b + c - 2) x y = true →
      thetaGenAdjB a b c x y = true)
    (hom : o + m ≤ a + b + c - 3) :
    (∀ j, j + 1 < m → F (o + j) ≠ F (o + j + 1)) ∧
      (1 ≤ m → F (a + b + c - 3) ≠ F (o + 0)) ∧
      (1 ≤ m → F (o + (m - 1)) ≠ F (a + b + c - 2)) ∧
      (m = 0 → F (a + b + c - 3) ≠ F (a + b + c - 2)) := by
  refine ⟨fun j hj => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · exact hadj _ _ (by omega) (by omega) (by omega) (harm _ _ (armStepB_mid o m _ _ j hj))
  · exact hadj _ _ (by omega) (by omega) (by omega)
      (harm _ _ (armStepB_head o m _ _ (by omega)))
  · exact hadj _ _ (by omega) (by omega) (by omega)
      (harm _ _ (armStepB_last o m _ _ (by omega)))
  · subst hm
    exact hadj _ _ (by omega) (by omega) (by omega) (harm _ _ (armStepB_direct o _ _))


/-! ### Combining the three arms -/

/-- The endgame for a shape with two arms of length `≥ 3`: the first arm decides, by its parity,
which diagonal of branch colors survives, and the other two arms kill the two survivors. -/
private lemma bad_finish {a x y : ℕ} (ha : 1 ≤ a) (hx : x = 1 ∨ x = 2) (hy : y = 1 ∨ y = 2)
    (key1 : x = y ↔ (a - 1) % 2 = 1)
    (hb2 : x = 1 → y ≠ (if a % 2 = 1 then 2 else 1))
    (hb3 : x = 2 → y ≠ (if a % 2 = 1 then 1 else 2)) : False := by
  rcases hx with hA | hA
  · have hbk := hb2 hA
    by_cases hpar : a % 2 = 1
    · rw [if_pos hpar] at hbk; omega
    · rw [if_neg hpar] at hbk; omega
  · have hbk := hb3 hA
    by_cases hpar : a % 2 = 1
    · rw [if_pos hpar] at hbk; omega
    · rw [if_neg hpar] at hbk; omega

/-- The endgame for a shape with `b = 2`: the three arms do not all have the same parity, so one
of them forces the two branch colors equal and another forces them different. -/
private lemma bad_finish_small {a b c x y : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b = 2)
    (key1 : x = y ↔ (a - 1) % 2 = 1) (key2 : x = y ↔ (b - 1) % 2 = 1)
    (key3 : x = y ↔ (c - 1) % 2 = 1) (hcodd : a = 2 → c % 2 = 1) : False := by
  have heq : x = y := key2.mpr (by omega)
  rcases (show a = 1 ∨ a = 2 from by omega) with h | h
  · have := key1.mp heq; omega
  · have := key3.mp heq; have := hcodd h; omega

/-! ### The witness assignment, read on indices -/

/-- `Monophilic.thetaBadLists` read as a function of the *index* of the vertex. -/
def badListAt (a b c i : ℕ) : Finset ℕ :=
  if b ≤ 2 then {1, 2}
  else if i + 1 < a then {1, 2}
  else if i + 2 < a + b then armBlockLists 1 (if a % 2 = 1 then 2 else 1) (b - 1) (i + 1 - a)
  else if i + 3 < a + b + c then
    armBlockLists 2 (if a % 2 = 1 then 1 else 2) (c - 1) (i + 2 - a - b)
  else {1, 2}

/-- The witness assignment depends on a vertex only through its index. -/
theorem thetaBadLists_apply (a b c : ℕ) (v : TGV a b c) :
    thetaBadLists a b c v = badListAt a b c v.val := rfl

/-- Every list of `Monophilic.armBlockLists` has two colors, as soon as the two prescribed branch
colors are `1` or `2`. -/
theorem card_armBlockLists {α β : ℕ} (hα : α = 1 ∨ α = 2) (hβ : β = 1 ∨ β = 2) (m j : ℕ) :
    (armBlockLists α β m j).card = 2 := by
  simp only [armBlockLists]
  split_ifs <;> exact Finset.card_pair (by omega)

/-- **The witness is a `2`-list assignment**, for every shape. -/
theorem card_thetaBadLists (a b c : ℕ) (v : TGV a b c) : (thetaBadLists a b c v).card = 2 := by
  rw [thetaBadLists_apply]
  simp only [badListAt]
  split_ifs <;>
    first
      | exact Finset.card_pair (by omega)
      | exact card_armBlockLists (by omega) (by omega) _ _

/-! ### No coloring from the witness -/

/-- **The witness assignment leaves no coloring at all**, stated entirely on indices: `F` is the
would-be coloring read through the index of a vertex. -/
private lemma thetaBad_no_index_coloring {a b c : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hb2 : 2 ≤ b) (hbad : ¬ GoodShape a b c) (F : ℕ → ℕ)
    (hmem : ∀ i, i < a + b + c - 1 → F i ∈ badListAt a b c i)
    (hadj : ∀ i j, i < a + b + c - 1 → j < a + b + c - 1 → i ≠ j →
      thetaGenAdjB a b c i j = true → F i ≠ F j) :
    False := by
  have hsum : 5 ≤ a + b + c := by omega
  have hSlist : badListAt a b c (a + b + c - 3) = ({1, 2} : Finset ℕ) := by
    simp only [badListAt]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hTlist : badListAt a b c (a + b + c - 2) = ({1, 2} : Finset ℕ) := by
    simp only [badListAt]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hα : F (a + b + c - 3) = 1 ∨ F (a + b + c - 3) = 2 := by
    have h := hmem (a + b + c - 3) (by omega)
    rw [hSlist] at h
    simpa using h
  have hβ : F (a + b + c - 2) = 1 ∨ F (a + b + c - 2) = 2 := by
    have h := hmem (a + b + c - 2) (by omega)
    rw [hTlist] at h
    simpa using h
  obtain ⟨s1, s2, s3, s4⟩ := arm_facts hsum F hadj 0 (a - 1) (thetaGenAdjB_arm1 a b c) (by omega)
  obtain ⟨t1, t2, t3, t4⟩ :=
    arm_facts hsum F hadj (a - 1) (b - 1) (thetaGenAdjB_arm2 a b c) (by omega)
  obtain ⟨u1, u2, u3, u4⟩ :=
    arm_facts hsum F hadj (a + b - 2) (c - 1) (thetaGenAdjB_arm3 a b c) (by omega)
  by_cases hbig : 3 ≤ b
  · -- two arms of length `≥ 3`: the first arm splits the four branch pairs by parity, and the
    -- other two each kill one of the two survivors
    have hL1 : ∀ j, j < a - 1 → F (0 + j) = 1 ∨ F (0 + j) = 2 := by
      intro j hj
      have h := hmem (0 + j) (by omega)
      rw [show badListAt a b c (0 + j) = ({1, 2} : Finset ℕ) from by
        simp only [badListAt, if_neg (show ¬ (b ≤ 2) from by omega),
          if_pos (show 0 + j + 1 < a from by omega)]] at h
      simpa using h
    have key1 : F (a + b + c - 3) = F (a + b + c - 2) ↔ (a - 1) % 2 = 1 :=
      const_block (fun j => F (0 + j)) hL1 s1 (fun hm => Ne.symm (s2 hm)) s3 s4 hα hβ
    have hL2 : ∀ j, j < b - 1 →
        F (a - 1 + j) ∈ armBlockLists 1 (if a % 2 = 1 then 2 else 1) (b - 1) j := by
      intro j hj
      have h := hmem (a - 1 + j) (by omega)
      rw [show badListAt a b c (a - 1 + j)
            = armBlockLists 1 (if a % 2 = 1 then 2 else 1) (b - 1) j from by
        simp only [badListAt, if_neg (show ¬ (b ≤ 2) from by omega),
          if_neg (show ¬ (a - 1 + j + 1 < a) from by omega),
          if_pos (show a - 1 + j + 2 < a + b from by omega)]
        congr 1
        omega] at h
      exact h
    have hL3 : ∀ j, j < c - 1 →
        F (a + b - 2 + j) ∈ armBlockLists 2 (if a % 2 = 1 then 1 else 2) (c - 1) j := by
      intro j hj
      have h := hmem (a + b - 2 + j) (by omega)
      rw [show badListAt a b c (a + b - 2 + j)
            = armBlockLists 2 (if a % 2 = 1 then 1 else 2) (c - 1) j from by
        simp only [badListAt, if_neg (show ¬ (b ≤ 2) from by omega),
          if_neg (show ¬ (a + b - 2 + j + 1 < a) from by omega),
          if_neg (show ¬ (a + b - 2 + j + 2 < a + b) from by omega),
          if_pos (show a + b - 2 + j + 3 < a + b + c from by omega)]
        congr 1
        omega] at h
      exact h
    have hblock2 : F (a + b + c - 3) = 1 →
        F (a + b + c - 2) ≠ (if a % 2 = 1 then 2 else 1) := by
      intro hA
      have h0 : F (a - 1 + 0) ≠ 1 := fun hcon => (t2 (by omega)) (by rw [hA, hcon])
      have hend := armBlockLists_forced 1 (if a % 2 = 1 then 2 else 1) (show 2 ≤ b - 1 by omega)
        (fun j => F (a - 1 + j)) hL2 t1 h0
      rw [← hend]
      exact Ne.symm (t3 (by omega))
    have hblock3 : F (a + b + c - 3) = 2 →
        F (a + b + c - 2) ≠ (if a % 2 = 1 then 1 else 2) := by
      intro hA
      have h0 : F (a + b - 2 + 0) ≠ 2 := fun hcon => (u2 (by omega)) (by rw [hA, hcon])
      have hend := armBlockLists_forced 2 (if a % 2 = 1 then 1 else 2) (show 2 ≤ c - 1 by omega)
        (fun j => F (a + b - 2 + j)) hL3 u1 h0
      rw [← hend]
      exact Ne.symm (u3 (by omega))
    exact bad_finish ha hα hβ key1 hblock2 hblock3
  · -- `b = 2`: the shape has an odd cycle, and the constant lists `{1, 2}` already fail
    have hb : b = 2 := by omega
    have hall : ∀ i, i < a + b + c - 1 → F i = 1 ∨ F i = 2 := by
      intro i hi
      have h := hmem i hi
      rw [show badListAt a b c i = ({1, 2} : Finset ℕ) from by
        simp only [badListAt, if_pos (show b ≤ 2 from by omega)]] at h
      simpa using h
    have key1 : F (a + b + c - 3) = F (a + b + c - 2) ↔ (a - 1) % 2 = 1 :=
      const_block (fun j => F (0 + j)) (fun j hj => hall _ (by omega)) s1
        (fun hm => Ne.symm (s2 hm)) s3 s4 hα hβ
    have key2 : F (a + b + c - 3) = F (a + b + c - 2) ↔ (b - 1) % 2 = 1 :=
      const_block (fun j => F (a - 1 + j)) (fun j hj => hall _ (by omega)) t1
        (fun hm => Ne.symm (t2 hm)) t3 t4 hα hβ
    have key3 : F (a + b + c - 3) = F (a + b + c - 2) ↔ (c - 1) % 2 = 1 :=
      const_block (fun j => F (a + b - 2 + j)) (fun j hj => hall _ (by omega)) u1
        (fun hm => Ne.symm (u2 hm)) u3 u4 hα hβ
    have hcodd : a = 2 → c % 2 = 1 := by
      intro ha2
      by_contra hc
      exact hbad ⟨ha2, hb, Nat.even_iff.mpr (by omega)⟩
    exact bad_finish_small ha hab hb key1 key2 key3 hcodd

/-- **`θ_{a,b,c}` has no coloring from `Monophilic.thetaBadLists`**, for every valid shape other
than Rubin's `(2, 2, \text{even})`. -/
theorem col_thetaBadLists_eq_zero {a b c : ℕ} (hv : ValidShape a b c) (hbad : ¬ GoodShape a b c) :
    (thetaGen a b c).col (thetaBadLists a b c) = 0 := by
  obtain ⟨ha, hab, hbc, hb2⟩ := hv
  rw [col_eq_zero_iff]
  intro f hmem hproper
  have hn : 0 < a + b + c - 1 := by omega
  refine thetaBad_no_index_coloring ha hab hbc hb2 hbad
    (fun i => f ⟨i % (a + b + c - 1), Nat.mod_lt i hn⟩) ?_ ?_
  · intro i hi
    have hEq : (⟨i % (a + b + c - 1), Nat.mod_lt i hn⟩ : TGV a b c) = ⟨i, hi⟩ :=
      Fin.val_injective (Nat.mod_eq_of_lt hi)
    simp only [hEq]
    exact hmem ⟨i, hi⟩
  · intro i j hi hj hij hB
    have hEi : (⟨i % (a + b + c - 1), Nat.mod_lt i hn⟩ : TGV a b c) = ⟨i, hi⟩ :=
      Fin.val_injective (Nat.mod_eq_of_lt hi)
    have hEj : (⟨j % (a + b + c - 1), Nat.mod_lt j hn⟩ : TGV a b c) = ⟨j, hj⟩ :=
      Fin.val_injective (Nat.mod_eq_of_lt hj)
    simp only [hEi, hEj]
    exact hproper (show (thetaGen a b c).Adj ⟨i, hi⟩ ⟨j, hj⟩ from
      ⟨fun hc => hij (congrArg Fin.val hc), Or.inl hB⟩)

/-! ### The classification -/

/-- **`θ_{a,b,c}` is not `2`-choosable**, for every valid shape other than Rubin's
`(2, 2, \text{even})`: the witness `Monophilic.thetaBadLists` is a `2`-list assignment with no
coloring at all. -/
theorem not_choosable_two_thetaGen {a b c : ℕ} (hv : ValidShape a b c)
    (hbad : ¬ GoodShape a b c) : ¬ (thetaGen a b c).Choosable 2 := by
  intro h
  have hpos := h (thetaBadLists a b c) (card_thetaBadLists a b c)
  rw [col_thetaBadLists_eq_zero hv hbad] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **The classification of `2`-choosable theta graphs**, discharging
`Monophilic.ThetaClassification`. -/
theorem thetaClassification : ThetaClassification :=
  fun _ _ _ hv hbad => not_choosable_two_thetaGen hv hbad

/-! ### Rubin's hard direction, with one hypothesis fewer -/

/-- **Rubin's hard direction, relative to `Monophilic.ThetaAlternative` alone.** -/
theorem rubinFamily_of_choosable' {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (halt : ThetaAlternative H) (hch : H.Choosable 2) : RubinFamily H :=
  rubinFamily_of_choosable thetaClassification H halt hch

/-- **Rubin's theorem as an `↔`, relative to `Monophilic.ThetaAlternative` alone.** -/
theorem choosable_two_iff_rubinFamily' {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (halt : ThetaAlternative H) : H.Choosable 2 ↔ RubinFamily H :=
  choosable_two_iff_rubinFamily thetaClassification H halt

/-- **Rubin's theorem over a core, relative to `Monophilic.ThetaAlternative` alone.** -/
theorem choosable_two_pendantTower_iff' {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (halt : ThetaAlternative H) (k : ℕ) (d : TowerData V k) :
    (pendantTower H k d).Choosable 2 ↔ RubinFamily H :=
  choosable_two_pendantTower_iff thetaClassification H halt k d

end Monophilic
