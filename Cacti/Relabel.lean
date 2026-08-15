/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.CycleCases

/-!
# The relabelling bridge: extension helpers

Connecting actual list colorings of a cycle to the transfer-matrix model needs two extension
constructions (handoff §6.2):

* a partial injection on `Fin k` extends to a permutation (`extendPerm`) — the completion `P`
  of the closing matching;
* an enumeration of a `k`-list extends to the next list matching shared colours
  (`extendEnum`) — the equality-extending relabelling step.

Both are the standard finite extension: fix the prescribed part, biject the leftovers.
-/

namespace ListColoring

open Finset

variable {k : ℕ}

/-- **Extending a partial injection to a permutation.** Given `f` injective on `s`, there is a
permutation of `Fin k` agreeing with `f` on `s`. -/
theorem exists_extendPerm (s : Finset (Fin k)) (f : Fin k → Fin k)
    (hinj : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b) :
    ∃ P : Equiv.Perm (Fin k), ∀ a ∈ s, P a = f a := by
  classical
  -- the prescribed part as an injection from `s` to `Fin k`
  have hcard : (s.image f).card = s.card := by
    rw [Finset.card_image_of_injOn (fun a ha b hb => hinj a ha b hb)]
  -- biject the complements
  have hcc : (sᶜ : Finset (Fin k)).card = ((s.image f)ᶜ : Finset (Fin k)).card := by
    rw [Finset.card_compl, Finset.card_compl, hcard]
  obtain ⟨g⟩ : Nonempty ((sᶜ : Finset (Fin k)) ≃ ((s.image f)ᶜ : Finset (Fin k))) :=
    ⟨Finset.equivOfCardEq hcc⟩
  -- assemble the total function
  set F : Fin k → Fin k := fun a => if ha : a ∈ s then f a else (g ⟨a, by simpa using ha⟩ : _)
    with hF
  have hFinj : Function.Injective F := by
    intro a b hab
    simp only [hF] at hab
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · rw [dif_pos ha, dif_pos hb] at hab
      exact hinj a ha b hb hab
    · rw [dif_pos ha, dif_neg hb] at hab
      exfalso
      have h1 : f a ∈ s.image f := Finset.mem_image_of_mem f ha
      have h2 := (g ⟨b, by simpa using hb⟩).property
      rw [← hab] at h2
      rw [Finset.mem_compl] at h2
      exact h2 h1
    · rw [dif_neg ha, dif_pos hb] at hab
      exfalso
      have h1 : f b ∈ s.image f := Finset.mem_image_of_mem f hb
      have h2 := (g ⟨a, by simpa using ha⟩).property
      rw [hab] at h2
      rw [Finset.mem_compl] at h2
      exact h2 h1
    · rw [dif_neg ha, dif_neg hb] at hab
      have := g.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
  refine ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.mp hFinj), ?_⟩
  intro a ha
  show F a = f a
  simp only [hF]
  exact dif_pos ha


/-- **Equality-extending enumeration step.** Given an enumeration of a `k`-list `A` and a
second `k`-list `B`, there is an enumeration of `B` agreeing with the first on shared
colours. -/
theorem exists_extendEnum {A B : Finset ℕ} (hA : A.card = k) (hB : B.card = k)
    (σ : Fin k → ℕ) (hσmem : ∀ i, σ i ∈ A) (hσinj : Function.Injective σ) :
    ∃ τ : Fin k → ℕ, (∀ i, τ i ∈ B) ∧ Function.Injective τ ∧
      ∀ i, σ i ∈ B → τ i = σ i := by
  classical
  set s : Finset (Fin k) := Finset.univ.filter (fun i => σ i ∈ B) with hs
  set img : Finset ℕ := s.image σ with himg
  have himgB : img ⊆ B := by
    intro x hx
    rw [himg, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [hs, Finset.mem_filter] at hi
    exact hi.2
  have himgcard : img.card = s.card := Finset.card_image_of_injective _ hσinj
  have hcc : (sᶜ : Finset (Fin k)).card = (B \ img).card := by
    rw [Finset.card_compl, Finset.card_sdiff_of_subset himgB, hB, himgcard, Fintype.card_fin]
  obtain ⟨g⟩ : Nonempty ((sᶜ : Finset (Fin k)) ≃ (B \ img : Finset ℕ)) :=
    ⟨Finset.equivOfCardEq hcc⟩
  set τ : Fin k → ℕ := fun i => if hi : i ∈ s then σ i else (g ⟨i, by simpa using hi⟩ : ℕ)
    with hτ
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro i
    simp only [hτ]
    by_cases hi : i ∈ s
    · rw [dif_pos hi]
      rw [hs, Finset.mem_filter] at hi
      exact hi.2
    · rw [dif_neg hi]
      have := (g ⟨i, by simpa using hi⟩).property
      rw [Finset.mem_sdiff] at this
      exact this.1
  · intro a b hab
    simp only [hτ] at hab
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · rw [dif_pos ha, dif_pos hb] at hab
      exact hσinj hab
    · rw [dif_pos ha, dif_neg hb] at hab
      exfalso
      have h1 : σ a ∈ img := by
        rw [himg]
        exact Finset.mem_image_of_mem σ ha
      have h2 := (g ⟨b, by simpa using hb⟩).property
      rw [← hab, Finset.mem_sdiff] at h2
      exact h2.2 h1
    · rw [dif_neg ha, dif_pos hb] at hab
      exfalso
      have h1 : σ b ∈ img := by
        rw [himg]
        exact Finset.mem_image_of_mem σ hb
      have h2 := (g ⟨a, by simpa using ha⟩).property
      rw [hab, Finset.mem_sdiff] at h2
      exact h2.2 h1
    · rw [dif_neg ha, dif_neg hb] at hab
      have := g.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
  · intro i hiB
    simp only [hτ]
    rw [dif_pos (by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hiB⟩)]


section Chain

variable {k : ℕ}

/-- An arbitrary enumeration of a `k`-list. -/
theorem exists_enum {A : Finset ℕ} (hA : A.card = k) :
    ∃ σ : Fin k → ℕ, (∀ i, σ i ∈ A) ∧ Function.Injective σ := by
  classical
  obtain ⟨g⟩ : Nonempty ((Finset.univ : Finset (Fin k)) ≃ A) :=
    ⟨Finset.equivOfCardEq (by rw [Finset.card_univ, Fintype.card_fin, hA])⟩
  refine ⟨fun i => (g ⟨i, Finset.mem_univ i⟩ : ℕ),
    fun i => (g ⟨i, Finset.mem_univ i⟩).property, ?_⟩
  intro a b hab
  have h2 := g.injective (Subtype.ext hab)
  have h3 := congrArg Subtype.val h2
  exact h3

/-- **The equality-extending enumeration chain**: enumerations of a path of `k`-lists, each
agreeing with the previous on shared colours. -/
theorem exists_enum_chain {n : ℕ} (hn : 1 ≤ n) (Ls : Fin n → Finset ℕ)
    (hLs : ∀ i, (Ls i).card = k) :
    ∃ σ : Fin n → Fin k → ℕ,
      (∀ i x, σ i x ∈ Ls i) ∧ (∀ i, Function.Injective (σ i)) ∧
      ∀ (i : Fin n) (h : i.val + 1 < n) (x : Fin k),
        σ i x ∈ Ls ⟨i.val + 1, h⟩ → σ ⟨i.val + 1, h⟩ x = σ i x := by
  classical
  obtain ⟨σ₀, hσ₀mem, hσ₀inj⟩ := exists_enum (hLs ⟨0, by omega⟩)
  have main : ∀ j, j < n → ∃ σs : Fin n → Fin k → ℕ,
      (∀ i : Fin n, i.val ≤ j → (∀ x, σs i x ∈ Ls i) ∧ Function.Injective (σs i)) ∧
      (∀ (i : Fin n) (h : i.val + 1 < n), i.val + 1 ≤ j → ∀ x,
        σs i x ∈ Ls ⟨i.val + 1, h⟩ → σs ⟨i.val + 1, h⟩ x = σs i x) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun _ => σ₀, fun i hi => ?_, fun i h h1 x => absurd h1 (by omega)⟩
      have hi0 : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        show i.val = 0
        omega
      rw [hi0]
      exact ⟨hσ₀mem, hσ₀inj⟩
    | succ j IHj =>
      intro hjn
      obtain ⟨σs, hmem, hmatch⟩ := IHj (by omega)
      have hj : (⟨j, by omega⟩ : Fin n).val ≤ j := le_refl j
      obtain ⟨hjm, hji⟩ := hmem ⟨j, by omega⟩ hj
      obtain ⟨τ, hτmem, hτinj, hτmatch⟩ :=
        exists_extendEnum (A := Ls ⟨j, by omega⟩) (B := Ls ⟨j + 1, hjn⟩)
          (hLs _) (hLs _) (σs ⟨j, by omega⟩) hjm hji
      refine ⟨Function.update σs ⟨j + 1, hjn⟩ τ, ?_, ?_⟩
      · intro i hi
        by_cases hij : i = ⟨j + 1, hjn⟩
        · rw [hij, Function.update_self]
          exact ⟨hτmem, hτinj⟩
        · rw [Function.update_of_ne hij]
          refine hmem i ?_
          have : i.val ≠ j + 1 := fun h => hij (Fin.ext h)
          omega
      · intro i h h1 x
        by_cases hij : (⟨i.val + 1, h⟩ : Fin n) = ⟨j + 1, hjn⟩
        · have hival : i.val = j := by
            have := congrArg Fin.val hij
            simpa using this
          have hjlt : j < n := Nat.lt_of_succ_lt hjn
          have hieq : i = (⟨j, hjlt⟩ : Fin n) := Fin.ext hival
          subst hieq
          have hine : (⟨j, by omega⟩ : Fin n) ≠ (⟨j + 1, hjn⟩ : Fin n) := by
            intro hcon
            have := congrArg Fin.val hcon
            simp at this
          intro hx
          rw [Function.update_of_ne hine] at hx
          rw [hij, Function.update_self, Function.update_of_ne hine]
          exact hτmatch x hx
        · have h2 : i.val + 1 ≤ j := by
            have : i.val + 1 ≠ j + 1 := fun hc => hij (Fin.ext hc)
            omega
          have hine : i ≠ (⟨j + 1, hjn⟩ : Fin n) := by
            intro hcon
            have := congrArg Fin.val hcon
            simp at this
            omega
          rw [Function.update_of_ne hij, Function.update_of_ne hine]
          exact hmatch i h h2 x
  obtain ⟨σs, hmem, hmatch⟩ := main (n - 1) (by omega)
  refine ⟨σs, fun i x => (hmem i (by omega)).1 x, fun i => (hmem i (by omega)).2,
    fun i h x => hmatch i h (by omega) x⟩

end Chain



section TransferCount

open Matrix

variable {k : ℕ}

/-- The factor entries, explicitly. -/
theorem factor_apply (T : Finset (Fin k)) (a x : Fin k) :
    (offDiag k + diagInd T) a x = if a = x then (if a ∈ T then 1 else 0) else 1 := by
  rw [Matrix.add_apply]
  show (if a = x then 0 else 1) + (if a = x ∧ a ∈ T then 1 else 0) = _
  by_cases hax : a = x
  · rw [if_pos hax, if_pos hax]
    by_cases haT : a ∈ T
    · rw [if_pos ⟨hax, haT⟩, if_pos haT]
    · rw [if_neg (fun h => haT h.2), if_neg haT]
  · rw [if_neg hax, if_neg (fun h => hax h.1), if_neg hax]

/-- The index-path count along a list of factors. -/
def pathCount (Ts : List (Finset (Fin k))) (a b : Fin k) : ℕ :=
  ((Finset.univ : Finset (Fin (Ts.length + 1) → Fin k)).filter
    (fun g => g 0 = a ∧ g (Fin.last _) = b ∧
      ∀ i : Fin Ts.length, (offDiag k + diagInd (Ts.get i)) (g i.castSucc) (g i.succ) = 1)).card

/-- **The transfer product counts index paths.** -/
theorem transferProd_apply_eq_pathCount (Ts : List (Finset (Fin k))) (a b : Fin k) :
    transferProd Ts a b = pathCount Ts a b := by
  induction Ts generalizing a with
  | nil =>
    rw [transferProd_nil, pathCount]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      refine (Finset.card_eq_one.mpr ⟨fun _ => a, ?_⟩).symm
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h0, -, -⟩
        funext i
        have hi : i = 0 := by
          apply Fin.ext
          show i.val = 0
          have := i.isLt
          simp only [List.length_nil] at this
          omega
        rw [hi, h0]
      · rintro rfl
        refine ⟨rfl, rfl, fun i => ?_⟩
        have h2 := i.isLt
        simp only [List.length_nil] at h2
        exact absurd h2 (Nat.not_lt_zero _)
    · rw [Matrix.one_apply_ne hab]
      refine (Finset.card_eq_zero.mpr ?_).symm
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      intro h0 hlast
      have h01 : (0 : Fin (([] : List (Finset (Fin k))).length + 1)) = Fin.last _ := by
        apply Fin.ext
        simp [Fin.last]
      exact fun _ => absurd (h0.symm.trans ((congrArg g h01).trans hlast)) hab
  | cons T Ts ih =>
    rw [transferProd_cons, Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun x _ => by rw [ih x])]
    -- partition the path count by the second vertex
    rw [pathCount, Finset.card_eq_sum_card_fiberwise
      (f := fun g => g 1) (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
    refine (Finset.sum_congr rfl fun x _ => ?_).symm
    -- per fibre: the head factor times the tail count
    by_cases hfac : (offDiag k + diagInd T) a x = 1
    · rw [hfac, Nat.one_mul, pathCount]
      refine Finset.card_nbij' (fun g => fun i => g i.succ)
        (fun h => Fin.cons a h) ?_ ?_ ?_ ?_
      · -- forward membership
        intro g hg
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
          Finset.mem_univ, true_and] at hg ⊢
        obtain ⟨⟨h0, hlast, hcomp⟩, h1⟩ := hg
        refine ⟨h1, ?_, ?_⟩
        · rw [← hlast]
          congr 1
        · intro i
          exact hcomp i.succ
      · -- backward membership
        intro h hh
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
          Finset.mem_univ, true_and] at hh ⊢
        obtain ⟨h0, hlast, hcomp⟩ := hh
        refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
        · rw [show (Fin.last (T :: Ts).length) = Fin.succ (Fin.last Ts.length) from
            (Fin.succ_last _).symm]
          rw [Fin.cons_succ]
          exact hlast
        · intro i
          refine Fin.cases ?_ ?_ i
          · rw [show ((0 : Fin (T :: Ts).length).castSucc) = 0 from rfl]
            rw [show ((0 : Fin (T :: Ts).length).succ) = Fin.succ 0 from rfl]
            rw [Fin.cons_zero, Fin.cons_succ]
            rw [show (T :: Ts).get 0 = T from rfl]
            rw [h0]
            exact hfac
          · intro j
            exact hcomp j
        · rw [show ((1 : Fin ((T :: Ts).length + 1))) = Fin.succ 0 from rfl,
            Fin.cons_succ]
          exact h0
      · -- left inverse
        intro g hg
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
          Finset.mem_univ, true_and] at hg
        funext i
        refine Fin.cases ?_ ?_ i
        · show a = g 0
          exact hg.1.1.symm
        · intro j
          rfl
      · -- right inverse
        intro h hh
        funext i
        rfl
    · -- the head factor is zero: the fibre is empty
      have hfac0 : (offDiag k + diagInd T) a x = 0 := by
        rw [factor_apply] at hfac ⊢
        by_cases hax : a = x
        · rw [if_pos hax] at hfac ⊢
          by_cases haT : a ∈ T
          · rw [if_pos haT] at hfac
            exact absurd rfl hfac
          · rw [if_neg haT]
        · rw [if_neg hax] at hfac
          exact absurd rfl hfac
      rw [hfac0, Nat.zero_mul]
      refine Finset.card_eq_zero.mpr ?_
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      intro hbig h1
      obtain ⟨h0, -, hcomp⟩ := hbig
      have := hcomp 0
      rw [show ((0 : Fin (T :: Ts).length).castSucc) = 0 from rfl,
        show ((0 : Fin (T :: Ts).length).succ) = 1 from rfl,
        show (T :: Ts).get 0 = T from rfl, h0, h1] at this
      rw [this] at hfac0
      exact absurd hfac0 one_ne_zero

end TransferCount



section BridgeLemmas

variable {k : ℕ}

/-- An injective enumeration of a `k`-list is onto it. -/
theorem enum_image {A : Finset ℕ} (hA : A.card = k) {σ : Fin k → ℕ}
    (hmem : ∀ i, σ i ∈ A) (hinj : Function.Injective σ) :
    Finset.univ.image σ = A := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hmem i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hA]

/-- Surjectivity of an enumeration onto its list. -/
theorem enum_surj {A : Finset ℕ} (hA : A.card = k) {σ : Fin k → ℕ}
    (hmem : ∀ i, σ i ∈ A) (hinj : Function.Injective σ) {y : ℕ} (hy : y ∈ A) :
    ∃ x, σ x = y := by
  rw [← enum_image hA hmem hinj, Finset.mem_image] at hy
  obtain ⟨x, -, hx⟩ := hy
  exact ⟨x, hx⟩

/-- **The factor characterizes colour compatibility** across an equality-extending step: the
entry is one exactly when the colours differ. -/
theorem factor_eq_one_iff {B : Finset ℕ} {σ τ : Fin k → ℕ}
    (hτmem : ∀ i, τ i ∈ B) (hτinj : Function.Injective τ)
    (hmatch : ∀ x, σ x ∈ B → τ x = σ x) (x y : Fin k) :
    (offDiag k + diagInd (Finset.univ.filter (fun z => σ z ≠ τ z))) x y = 1 ↔ σ x ≠ τ y := by
  rw [factor_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    by_cases hT : x ∈ Finset.univ.filter (fun z => σ z ≠ τ z)
    · rw [if_pos hT]
      rw [Finset.mem_filter] at hT
      exact ⟨fun _ => hT.2, fun _ => rfl⟩
    · rw [if_neg hT]
      rw [Finset.mem_filter] at hT
      push Not at hT
      have h2 := hT (Finset.mem_univ x)
      constructor
      · intro h
        exact absurd h (by omega)
      · intro h
        exact absurd h2 h
  · rw [if_neg hxy]
    refine ⟨fun _ hcon => ?_, fun _ => rfl⟩
    have hB : σ x ∈ B := hcon ▸ hτmem y
    have h2 : τ x = σ x := hmatch x hB
    exact hxy (hτinj (h2.trans hcon))

end BridgeLemmas

end ListColoring
