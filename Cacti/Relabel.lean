/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.CycleCases
import Cacti.Rooted

/-!
# The relabelling bridge

List colorings of a cycle counted by the transfer-matrix model (handoff §6.2). Two finite
extensions carry the relabelling — fix the prescribed part, biject the leftovers:

* a partial injection on `Fin k` extends to a permutation (`exists_extendPerm`) — the
  completion `P` of the closing matching;
* an enumeration of a `k`-list extends to the next list matching shared colours
  (`exists_extendEnum`), and along a path to the whole chain (`exists_enum_chain`).

On top of them:

* `transferProd_apply_eq_pathCount` / `sum_transferProd_ofFn` — the transfer product counts
  index paths, and its row sums count paths into a set of endpoints;
* `rootedCol_eq_rootCount` — the count identity: under the chain, rooted colorings at the root
  colour `σ 0 c` are the `c`-row of the transfer product, closed by `P` where the closing edge
  binds and left open where the root colour misses the last list;
* `exists_matrix_model` — the model with the thread splits its twisted labels force;
* `rootedCol_constList_cycle` — against the constant list the model degenerates to the pure
  power, giving the uniform normalizer `A`.
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

/-- The path count against an external length: the list's length rewritten to a variable. -/
theorem pathCount_eq_card {n : ℕ} {Ts : List (Finset (Fin k))} (h : Ts.length = n) (a b : Fin k) :
    pathCount Ts a b =
      (Finset.univ.filter (fun g : Fin (n + 1) → Fin k =>
        g 0 = a ∧ g (Fin.last n) = b ∧
        ∀ e : Fin n, (offDiag k + diagInd (Ts.get (Fin.cast h.symm e)))
          (g e.castSucc) (g e.succ) = 1)).card := by
  subst h
  rfl

/-- **Index paths into a set of endpoints**: the transfer product of `List.ofFn T`, summed over
a set of right endpoints, counts the index paths ending in that set. -/
theorem sum_transferProd_ofFn {n : ℕ} (T : Fin n → Finset (Fin k)) (a : Fin k)
    (S : Finset (Fin k)) :
    ∑ b ∈ S, transferProd (List.ofFn T) a b =
      (Finset.univ.filter (fun g : Fin (n + 1) → Fin k =>
        g 0 = a ∧ g (Fin.last n) ∈ S ∧
        ∀ e : Fin n, (offDiag k + diagInd (T e)) (g e.castSucc) (g e.succ) = 1)).card := by
  classical
  have hget : ∀ e : Fin n,
      (List.ofFn T).get (Fin.cast (List.length_ofFn (f := T)).symm e) = T e :=
    fun e => List.get_ofFn T _
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (n + 1) → Fin k => g (Fin.last n))
    (t := S) (fun g hg => by
      simp only [Finset.mem_coe, Finset.mem_filter] at hg
      exact hg.2.2.1)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [transferProd_apply_eq_pathCount, pathCount_eq_card (List.length_ofFn) a b]
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hget]
  constructor
  · rintro ⟨h0, hlast, hedge⟩
    exact ⟨⟨h0, hlast ▸ hb, hedge⟩, hlast⟩
  · rintro ⟨⟨h0, -, hedge⟩, hlast⟩
    exact ⟨h0, hlast, hedge⟩

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


section Surgery

/-- **One-position list surgery.** -/
theorem exists_one_split {α : Type _} : ∀ (l : List α) (j : ℕ) (hj : j < l.length),
    ∃ (l₂ : List α) (y : α) (l₃ : List α),
      l = l₂ ++ y :: l₃ ∧ l₂.length = j ∧ y = l.get ⟨j, hj⟩
  | a :: l, 0, _ => ⟨[], a, l, rfl, rfl, rfl⟩
  | a :: l, j + 1, hj => by
      obtain ⟨l₂, y, l₃, heq, hlen, hget⟩ := exists_one_split l j (by
        rw [List.length_cons] at hj
        omega)
      exact ⟨a :: l₂, y, l₃, by rw [List.cons_append, ← heq],
        by rw [List.length_cons, hlen], hget⟩

/-- **Two-position list surgery**: positions `i < j` split a list into the five-part form the
thread hypothesis consumes. -/
theorem exists_two_split {α : Type _} (l : List α) (i j : ℕ) (hij : i < j)
    (hj : j < l.length) :
    ∃ (l₁ : List α) (x : α) (l₂ : List α) (y : α) (l₃ : List α),
      l = l₁ ++ x :: (l₂ ++ y :: l₃) ∧ l₁.length = i ∧ l₁.length + 1 + l₂.length = j ∧
      x = l.get ⟨i, by omega⟩ ∧ y = l.get ⟨j, hj⟩ := by
  obtain ⟨l₁, x, rest, he1, hl1, hx⟩ := exists_one_split l i (by omega)
  subst he1
  have hrest : j - i - 1 < rest.length := by
    rw [List.length_append, List.length_cons] at hj
    omega
  obtain ⟨l₂, y, l₃, he2, hl2, hy⟩ := exists_one_split rest (j - i - 1) hrest
  subst he2
  rw [List.length_append, List.length_cons, List.length_append, List.length_cons] at hj
  refine ⟨l₁, x, l₂, y, l₃, rfl, hl1, by omega, hx, ?_⟩
  show y = (l₁ ++ x :: (l₂ ++ y :: l₃))[j]'(by
    rw [List.length_append, List.length_cons, List.length_append, List.length_cons]
    omega)
  rw [List.getElem_append_right (by omega)]
  simp only [show j - l₁.length = (j - i - 1) + 1 from by omega, List.getElem_cons_succ]
  exact hy

end Surgery




section MatrixModel

open SimpleGraph Finset

/-- The successor in `Fin (m+1)` is either a step along the path or the closing wrap. -/
theorem fin_succ_cases {m : ℕ} {i j : Fin (m + 1)} (h : j = i + 1) :
    (∃ e : Fin m, i = e.castSucc ∧ j = e.succ) ∨ (i = Fin.last m ∧ j = 0) := by
  by_cases hi : i.val < m
  · refine Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl, Fin.ext ?_⟩
    rw [h, Fin.val_add_one_of_lt (Fin.lt_def.mpr (by simpa using hi)), Fin.val_succ]
  · have hlast : i = Fin.last m := Fin.ext (by
      rw [Fin.val_last]
      have := i.isLt
      omega)
    exact Or.inr ⟨hlast, by rw [h, hlast, Fin.last_add_one]⟩

/-- **The count identity of the matrix model**: for a cyclically indexed graph with an
equality-extending enumeration chain `σ`, the rooted count at the root colour `σ 0 c` is the
`c`-row of the transfer product, closed by `P` at the defined roots. -/
theorem rootedCol_eq_rootCount {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {m k : ℕ} (w : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (w i) (w j) ↔ (j = i + 1 ∨ i = j + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L k)
    (σ : Fin (m + 1) → Fin k → ℕ)
    (hσmem : ∀ i x, σ i x ∈ L (w i)) (hσinj : ∀ i, Function.Injective (σ i))
    (hσmatch : ∀ (i : Fin (m + 1)) (h : i.val + 1 < m + 1) (x : Fin k),
      σ i x ∈ L (w ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (P : Equiv.Perm (Fin k)) (dom : Finset (Fin k))
    (hdom : ∀ c, c ∈ dom ↔ σ 0 c ∈ L (w (Fin.last m)))
    (hP : ∀ c ∈ dom, σ (Fin.last m) (P.symm c) = σ 0 c) (c : Fin k) :
    rootedCol G L (w 0) (σ 0 c)
      = rootCount (List.ofFn (fun e : Fin m =>
          Finset.univ.filter (fun x => σ e.castSucc x ≠ σ e.succ x))) P dom c := by
  classical
  set T : Fin m → Finset (Fin k) :=
    fun e => Finset.univ.filter (fun x => σ e.castSucc x ≠ σ e.succ x) with hT
  set S : Finset (Fin k) := if c ∈ dom then Finset.univ.erase (P.symm c) else Finset.univ with hS
  -- the closing datum turns the root count into a row sum over `S`
  have hrc : rootCount (List.ofFn T) P dom c = ∑ b ∈ S, transferProd (List.ofFn T) c b := by
    rw [rootCount, hS]
    by_cases hc : c ∈ dom
    · rw [if_pos hc, if_pos hc, mulOffPerm_diag]
    · rw [if_neg hc, if_neg hc]
  rw [hrc, sum_transferProd_ofFn]
  -- the factor entry is exactly colour compatibility across a path edge
  have hfac : ∀ (e : Fin m) (x y : Fin k),
      (offDiag k + diagInd (T e)) x y = 1 ↔ σ e.castSucc x ≠ σ e.succ y := by
    intro e x y
    have hlt : (Fin.castSucc e : Fin (m + 1)).val + 1 < m + 1 := by
      have := e.isLt
      simp only [Fin.val_castSucc]
      omega
    have hcast : (⟨(Fin.castSucc e : Fin (m + 1)).val + 1, hlt⟩ : Fin (m + 1)) = e.succ :=
      Fin.ext (by simp)
    refine factor_eq_one_iff (B := L (w e.succ)) (fun i => hσmem e.succ i) (hσinj e.succ)
      (fun z hz => ?_) x y
    have h2 := hσmatch (Fin.castSucc e) hlt z (by rw [hcast]; exact hz)
    rwa [hcast] at h2
  have hpath : ∀ e : Fin m, G.Adj (w e.castSucc) (w e.succ) :=
    fun e => (hadj _ _).mpr (Or.inl Fin.coeSucc_eq_succ.symm)
  have hclose : G.Adj (w (Fin.last m)) (w 0) :=
    (hadj _ _).mpr (Or.inl (Fin.last_add_one m).symm)
  rw [rootedCol]
  refine (Finset.card_bij (fun g _ => (fun v => σ (w.symm v) (g (w.symm v)))) ?_ ?_ ?_).symm
  · -- an index path is a rooted colouring
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨h0, hlast, hedge⟩ := hg
    have key : ∀ i j : Fin (m + 1), j = i + 1 → σ i (g i) ≠ σ j (g j) := by
      intro i j hij
      rcases fin_succ_cases hij with ⟨e, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hfac e _ _).mp (hedge e)
      · intro hcon
        rw [h0] at hcon
        by_cases hc : c ∈ dom
        · rw [hS, if_pos hc] at hlast
          exact Finset.ne_of_mem_erase hlast
            (hσinj (Fin.last m) (hcon.trans (hP c hc).symm))
        · exact (hdom c).not.mp hc (hcon ▸ hσmem (Fin.last m) (g (Fin.last m)))
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
    refine ⟨⟨fun v => ?_, fun u v huv => ?_⟩, ?_⟩
    · have := hσmem (w.symm v) (g (w.symm v))
      rwa [Equiv.apply_symm_apply] at this
    · have h1 : G.Adj (w (w.symm u)) (w (w.symm v)) := by
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact huv
      rcases (hadj _ _).mp h1 with h | h
      · exact key _ _ h
      · exact (key _ _ h).symm
    · show σ (w.symm (w 0)) (g (w.symm (w 0))) = σ 0 c
      rw [Equiv.symm_apply_apply, h0]
  · -- distinct index paths give distinct colourings
    intro g₁ h₁ g₂ h₂ heq
    funext i
    have hi := congrFun heq (w i)
    simp only [Equiv.symm_apply_apply] at hi
    exact hσinj i hi
  · -- every rooted colouring is an index path
    intro f hf
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff] at hf
    obtain ⟨⟨hfmem, hfprop⟩, hfroot⟩ := hf
    choose g hgi using fun i : Fin (m + 1) =>
      enum_surj (hL (w i)) (hσmem i) (hσinj i) (hfmem (w i))
    refine ⟨g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hσinj 0 ((hgi 0).trans hfroot), ?_, fun e => ?_⟩
      · by_cases hc : c ∈ dom
        · rw [hS, if_pos hc]
          refine Finset.mem_erase.mpr ⟨fun hcon => ?_, Finset.mem_univ _⟩
          refine hfprop _ _ hclose ?_
          rw [← hgi (Fin.last m), hcon, hP c hc, hfroot]
        · rw [hS, if_neg hc]
          exact Finset.mem_univ _
      · refine (hfac e _ _).mpr ?_
        rw [hgi e.castSucc, hgi e.succ]
        exact hfprop _ _ (hpath e)
    · funext v
      rw [hgi (w.symm v), Equiv.apply_symm_apply]

/-- **The matrix model of a listed cycle** (the relabelling bridge, handoff §6.2): every
cyclically indexed graph with `k`-lists is counted by the transfer-matrix model, with the
thread splits of its twisted closing labels. -/
theorem exists_matrix_model {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {m : ℕ} (w : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (w i) (w j) ↔ (j = i + 1 ∨ i = j + 1))
    {k : ℕ} (L : ListAssignment V) (hL : IsNListAssignment L k) :
    ∃ (Ts : List (Finset (Fin k))) (P : Equiv.Perm (Fin k)) (dom : Finset (Fin k))
      (σ₀ : Fin k → ℕ),
      Ts.length = m ∧ (∀ i, σ₀ i ∈ L (w 0)) ∧ Function.Injective σ₀ ∧
      (∀ c, rootedCol G L (w 0) (σ₀ c) = rootCount Ts P dom c) ∧
      (∀ c ∈ dom, P.symm c ≠ c →
        ∃ (Ts₁ : List (Finset (Fin k))) (T : Finset (Fin k)) (Ts₂ : List (Finset (Fin k)))
          (T' : Finset (Fin k)) (Ts₃ : List (Finset (Fin k))),
          Ts = Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃) ∧ c ∈ T ∧ P.symm c ∈ T') := by
  classical
  -- the equality-extending chain along the path
  obtain ⟨σ, hσmem, hσinj, hσmatch⟩ := exists_enum_chain (by omega)
    (fun i : Fin (m + 1) => L (w i)) (fun i => hL (w i))
  -- the survivor complements along the path edges
  set Ts : List (Finset (Fin k)) := List.ofFn
    (fun e : Fin m => Finset.univ.filter (fun x => σ e.castSucc x ≠ σ e.succ x)) with hTs
  have hTslen : Ts.length = m := by rw [hTs, List.length_ofFn]
  -- the closing data
  set dom : Finset (Fin k) := Finset.univ.filter
    (fun c => σ 0 c ∈ L (w (Fin.last m))) with hdom
  have hμex : ∀ c ∈ dom, ∃ x, σ (Fin.last m) x = σ 0 c := by
    intro c hc
    rw [hdom, Finset.mem_filter] at hc
    exact enum_surj (hL (w (Fin.last m))) (hσmem (Fin.last m)) (hσinj (Fin.last m)) hc.2
  set μ : Fin k → Fin k := fun c => if hc : c ∈ dom then Classical.choose (hμex c hc) else c
    with hμ
  have hμspec : ∀ c (hc : c ∈ dom), σ (Fin.last m) (μ c) = σ 0 c := by
    intro c hc
    simp only [hμ]
    rw [dif_pos hc]
    exact Classical.choose_spec (hμex c hc)
  have hμinj : ∀ c ∈ dom, ∀ c' ∈ dom, μ c = μ c' → c = c' := by
    intro c hc c' hc' hcc
    have h1 := hμspec c hc
    have h2 := hμspec c' hc'
    rw [hcc, h2] at h1
    exact hσinj 0 h1.symm
  -- the completed permutation: on the image of μ, send μ c back to c
  have hgex : ∀ a ∈ dom.image μ, ∃ c ∈ dom, μ c = a := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨c, hc, hca⟩ := ha
    exact ⟨c, hc, hca⟩
  set g : Fin k → Fin k := fun a => if ha : a ∈ dom.image μ then
      Classical.choose (hgex a ha) else a
    with hg
  have hgspec : ∀ a (ha : a ∈ dom.image μ),
      Classical.choose (hgex a ha) ∈ dom ∧ μ (Classical.choose (hgex a ha)) = a := by
    intro a ha
    exact ⟨(Classical.choose_spec (hgex a ha)).1, (Classical.choose_spec (hgex a ha)).2⟩
  obtain ⟨P, hP⟩ := exists_extendPerm (dom.image μ) g (by
    intro a ha b hb hab
    simp only [hg] at hab
    rw [dif_pos ha, dif_pos hb] at hab
    obtain ⟨hca, hμa⟩ := hgspec a ha
    obtain ⟨hcb, hμb⟩ := hgspec b hb
    rw [← hμa, ← hμb, hab])
  have hPμ : ∀ c ∈ dom, P (μ c) = c := by
    intro c hc
    have hmem : μ c ∈ dom.image μ := Finset.mem_image_of_mem μ hc
    rw [hP _ hmem]
    simp only [hg]
    rw [dif_pos hmem]
    obtain ⟨hc', hμ'⟩ := hgspec (μ c) hmem
    exact hμinj _ hc' _ hc hμ'
  have hPsymm : ∀ c ∈ dom, P.symm c = μ c := by
    intro c hc
    have h1 := hPμ c hc
    have h2 : P.symm c = P.symm (P (μ c)) := by rw [h1]
    rw [h2, Equiv.symm_apply_apply]
  refine ⟨Ts, P, dom, σ 0, hTslen, hσmem 0, hσinj 0, ?_, ?_⟩
  · -- the count identity
    intro c
    rw [hTs]
    exact rootedCol_eq_rootCount w hadj L hL σ hσmem hσinj hσmatch P dom
      (fun c => by
        rw [hdom, Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩)
      (fun c hc => by rw [hPsymm c hc]; exact hμspec c hc) c
  · -- the thread splits
    intro c hc htw
    rw [hPsymm c hc] at htw ⊢
    set E1 : Finset (Fin m) := Finset.univ.filter
      (fun e => σ e.castSucc c ≠ σ e.succ c) with hE1
    set E2 : Finset (Fin m) := Finset.univ.filter
      (fun e => σ e.castSucc (μ c) ≠ σ e.succ (μ c)) with hE2
    have hconst : ∀ (x : Fin k) (v : ℕ) (hv : v < m + 1),
        (∀ e : Fin m, e.val < v → σ e.castSucc x = σ e.succ x) →
        σ ⟨v, hv⟩ x = σ 0 x := by
      intro x v
      induction v with
      | zero =>
        intro _ _
        rfl
      | succ v ihv =>
        intro hv hagree
        have hvm : v < m := by omega
        have h2 := hagree ⟨v, hvm⟩ (by show v < v + 1; omega)
        have h2' : σ (⟨v + 1, hv⟩ : Fin (m + 1)) x
            = σ (⟨v, by omega⟩ : Fin (m + 1)) x := h2.symm
        exact h2'.trans (ihv (by omega) (fun e he => hagree e (by omega)))
    have hconst' : ∀ (x : Fin k) (d v : ℕ), m - v = d → ∀ (hv : v < m + 1),
        (∀ e : Fin m, v ≤ e.val → σ e.castSucc x = σ e.succ x) →
        σ ⟨v, hv⟩ x = σ (Fin.last m) x := by
      intro x d
      induction d with
      | zero =>
        intro v hd hv _
        have hvm : v = m := by omega
        subst hvm
        rfl
      | succ d ihd =>
        intro v hd hv hagree
        have hvm : v < m := by omega
        have h2 := hagree ⟨v, hvm⟩ (le_refl v)
        have h2' : σ (⟨v, hv⟩ : Fin (m + 1)) x
            = σ (⟨v + 1, by omega⟩ : Fin (m + 1)) x := h2
        exact h2'.trans (ihd (v + 1) (by omega) (by omega) (fun e he => hagree e (by omega)))
    have hE1ne : E1.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hagree : ∀ e : Fin m, σ e.castSucc c = σ e.succ c := by
        intro e
        by_contra hne
        have hmem : e ∈ E1 := by
          rw [hE1, Finset.mem_filter]
          exact ⟨Finset.mem_univ e, hne⟩
        rw [hcon] at hmem
        exact absurd hmem (Finset.notMem_empty e)
      have h1 : σ (⟨m, by omega⟩ : Fin (m + 1)) c = σ 0 c :=
        hconst c m (by omega) (fun e _ => hagree e)
      have h2 : σ (Fin.last m) (μ c) = σ 0 c := hμspec c hc
      exact htw (hσinj (Fin.last m) (h2.trans h1.symm))
    have hE2ne : E2.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hagree : ∀ e : Fin m, σ e.castSucc (μ c) = σ e.succ (μ c) := by
        intro e
        by_contra hne
        have hmem : e ∈ E2 := by
          rw [hE2, Finset.mem_filter]
          exact ⟨Finset.mem_univ e, hne⟩
        rw [hcon] at hmem
        exact absurd hmem (Finset.notMem_empty e)
      have h1 : σ (⟨0, by omega⟩ : Fin (m + 1)) (μ c) = σ (Fin.last m) (μ c) :=
        hconst' (μ c) m 0 (by omega) (by omega) (fun e _ => hagree e)
      have h2 : σ (Fin.last m) (μ c) = σ 0 c := hμspec c hc
      refine htw (hσinj 0 ?_)
      show σ 0 (μ c) = σ 0 c
      rw [← h2, ← h1]
      rfl
    set i := E1.min' hE1ne with hi
    set j := E2.max' hE2ne with hj
    have hij : i.val < j.val := by
      by_contra hcon
      push Not at hcon
      have hbelow : ∀ e : Fin m, e.val < j.val → σ e.castSucc c = σ e.succ c := by
        intro e he
        by_contra hne
        have hmem : e ∈ E1 := by
          rw [hE1, Finset.mem_filter]
          exact ⟨Finset.mem_univ e, hne⟩
        have h5 : i.val ≤ e.val := E1.min'_le e hmem
        omega
      have habove : ∀ e : Fin m, j.val < e.val →
          σ e.castSucc (μ c) = σ e.succ (μ c) := by
        intro e he
        by_contra hne
        have hmem : e ∈ E2 := by
          rw [hE2, Finset.mem_filter]
          exact ⟨Finset.mem_univ e, hne⟩
        have h5 : e.val ≤ j.val := E2.le_max' e hmem
        omega
      have hjlt : j.val < m + 1 := by
        have := j.isLt
        omega
      have hjlt' : j.val + 1 < m + 1 := by
        have := j.isLt
        omega
      have hχc : σ (⟨j.val, hjlt⟩ : Fin (m + 1)) c = σ 0 c :=
        hconst c j.val hjlt (fun e he => hbelow e he)
      have hχμ : σ (⟨j.val + 1, hjlt'⟩ : Fin (m + 1)) (μ c) = σ (Fin.last m) (μ c) :=
        hconst' (μ c) (m - (j.val + 1)) (j.val + 1) rfl hjlt'
          (fun e he => habove e (by omega))
      have hmem2 : σ (⟨j.val, hjlt⟩ : Fin (m + 1)) c
          ∈ L (w ⟨j.val + 1, hjlt'⟩) := by
        rw [hχc, ← hμspec c hc, ← hχμ]
        exact hσmem _ _
      have hmatch2 := hσmatch ⟨j.val, hjlt⟩ hjlt' c hmem2
      have hcol : σ (⟨j.val + 1, hjlt'⟩ : Fin (m + 1)) c
          = σ (⟨j.val + 1, hjlt'⟩ : Fin (m + 1)) (μ c) := by
        rw [hmatch2, hχc, ← hμspec c hc, ← hχμ]
      exact absurd (hσinj _ hcol).symm htw
    obtain ⟨Ts₁, T, Ts₂, T', Ts₃, hsplit, hl1, hl2, hxget, hyget⟩ :=
      exists_two_split Ts i.val j.val hij (by rw [hTslen]; exact j.isLt)
    refine ⟨Ts₁, T, Ts₂, T', Ts₃, hsplit, ?_, ?_⟩
    · rw [hxget]
      have hbound : i.val < Ts.length := by rw [hTslen]; exact i.isLt
      rw [List.get_eq_getElem]
      have hget : Ts[i.val]'hbound
          = Finset.univ.filter (fun x => σ i.castSucc x ≠ σ i.succ x) := by
        simp only [hTs, List.getElem_ofFn]
      rw [hget, Finset.mem_filter]
      refine ⟨Finset.mem_univ c, ?_⟩
      have hmm : i ∈ Finset.univ.filter (fun e => σ e.castSucc c ≠ σ e.succ c) :=
        E1.min'_mem hE1ne
      rw [Finset.mem_filter] at hmm
      exact hmm.2
    · rw [hyget]
      have hbound : j.val < Ts.length := by rw [hTslen]; exact j.isLt
      rw [List.get_eq_getElem]
      have hget : Ts[j.val]'hbound
          = Finset.univ.filter (fun x => σ j.castSucc x ≠ σ j.succ x) := by
        simp only [hTs, List.getElem_ofFn]
      rw [hget, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmm : j ∈ Finset.univ.filter (fun e => σ e.castSucc (μ c) ≠ σ e.succ (μ c)) :=
        E2.max'_mem hE2ne
      rw [Finset.mem_filter] at hmm
      exact hmm.2

/-- **The uniform rooted count of a cycle**: against the constant list every label survives, so
the model degenerates to the pure power and the rooted count is the normalizer `A`. -/
theorem rootedCol_constList_cycle {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {m k : ℕ} (hk : 1 ≤ k) (w : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (w i) (w j) ↔ (j = i + 1 ∨ i = j + 1)) :
    rootedCol G (constList V k) (w 0) 0 = uniformA k (m + 1) := by
  classical
  have h := rootedCol_eq_rootCount w hadj (constList V k) (isNListAssignment_constList k)
    (fun _ x => (x : ℕ))
    (fun i x => by simp [constList_apply, Finset.mem_range, x.isLt])
    (fun _ a b hab => Fin.val_injective hab)
    (fun _ _ _ _ => rfl)
    (1 : Equiv.Perm (Fin k)) Finset.univ
    (fun c => by simp [constList_apply, Finset.mem_range, c.isLt])
    (fun _ _ => rfl) ⟨0, hk⟩
  have hTs : (List.ofFn (fun _ : Fin m =>
      Finset.univ.filter (fun x : Fin k => ((x : ℕ)) ≠ ((x : ℕ))))) =
      List.replicate m (∅ : Finset (Fin k)) := by
    rw [← List.ofFn_const]
    congr
    funext e
    simp
  rw [h, hTs, rootCount, if_pos (Finset.mem_univ _), transferProd_replicate_empty,
    base_diag_fixed hk 1 rfl, uniformA, Nat.add_sub_cancel]

end MatrixModel


end ListColoring
