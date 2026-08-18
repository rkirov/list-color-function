/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Relabel

namespace ListColoring

open Finset Matrix

variable {k : ℕ}

/-- The completed-cover coloring set, as index functions: consecutive indices differ along the
path, and the closing pair is forbidden through `P`. -/
def coverSet (P : Equiv.Perm (Fin k)) (m : ℕ) : Finset (Fin (m + 1) → Fin k) :=
  Finset.univ.filter (fun g => (∀ e : Fin m, g e.castSucc ≠ g e.succ) ∧ P (g (Fin.last m)) ≠ g 0)

theorem offDiag_apply_eq_one_iff (x y : Fin k) : offDiag k x y = 1 ↔ x ≠ y := by
  show (if x = y then 0 else 1) = 1 ↔ _
  by_cases h : x = y <;> simp [h]

/-- **L3**: the cover count at the root is the base diagonal entry. -/
theorem card_cover_root (P : Equiv.Perm (Fin k)) (m : ℕ) (d : Fin k) :
    ((coverSet P m).filter (fun g => g 0 = d)).card = ((offDiag k ^ m) * offPerm P) d d := by
  classical
  have h := sum_transferProd_ofFn (n := m) (fun _ : Fin m => (∅ : Finset (Fin k))) d
      (Finset.univ.erase (P.symm d))
  have hpow : transferProd (List.ofFn (fun _ : Fin m => (∅ : Finset (Fin k))))
      = offDiag k ^ m := by
    rw [List.ofFn_const, transferProd_replicate_empty]
  rw [hpow] at h
  rw [mulOffPerm_diag, h]
  congr 1
  ext g
  simp only [coverSet, Finset.mem_filter, Finset.mem_univ, true_and, diagInd_empty, add_zero,
    Finset.mem_erase]
  constructor
  · rintro ⟨⟨hpath, hclose⟩, h0⟩
    refine ⟨h0, ⟨?_, trivial⟩, fun e => (offDiag_apply_eq_one_iff _ _).mpr (hpath e)⟩
    intro hcon
    exact hclose (by rw [hcon, Equiv.apply_symm_apply, h0])
  · rintro ⟨h0, ⟨hlast, -⟩, hedge⟩
    refine ⟨⟨fun e => (offDiag_apply_eq_one_iff _ _).mp (hedge e), ?_⟩, h0⟩
    rw [h0]
    intro hcon
    exact hlast (by rw [← hcon, Equiv.symm_apply_apply])

/-- **L6**: the base diagonal is `A` at a fixed label and `A + 1` at a moved one, on odd cycles. -/
theorem cover_diag_value (hk : 2 ≤ k) {m : ℕ} (hm : Even m) (P : Equiv.Perm (Fin k)) (d : Fin k) :
    ((offDiag k ^ m) * offPerm P) d d
      = uniformA k (m + 1) + (if P.symm d = d then 0 else 1) := by
  by_cases hfix : P.symm d = d
  · rw [if_pos hfix, base_diag_fixed (by omega) P hfix, uniformA, Nat.add_sub_cancel, Nat.add_zero]
  · rw [if_neg hfix, base_diag_moved (by omega) P hfix, uniformA, Nat.add_sub_cancel]
    have halt : alpha k m = beta k m + 1 := (beta_alternation hk m).2 hm
    rw [halt, show k - 1 = 1 + (k - 2) from by omega]
    ring



section Rotate

variable {m : ℕ}

/-- One-step rotation of an index function, twisted by `P⁻¹` across the closing edge. -/
def rot1 (P : Equiv.Perm (Fin k)) (g : Fin (m + 1) → Fin k) : Fin (m + 1) → Fin k :=
  fun t => if h : t.val < m then g ⟨t.val + 1, by omega⟩ else P.symm (g 0)

/-- Its inverse. -/
def unrot1 (P : Equiv.Perm (Fin k)) (h : Fin (m + 1) → Fin k) : Fin (m + 1) → Fin k :=
  fun s => if hs : 0 < s.val then h ⟨s.val - 1, by omega⟩ else P (h (Fin.last m))

theorem rot1_mem (hm : 1 ≤ m) (P : Equiv.Perm (Fin k)) {g : Fin (m + 1) → Fin k}
    (hg : g ∈ coverSet P m) : rot1 P g ∈ coverSet P m := by
  simp only [coverSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
  obtain ⟨hpath, hclose⟩ := hg
  constructor
  · intro e
    have hc : (e.castSucc).val = e.val := rfl
    have hs : (e.succ).val = e.val + 1 := rfl
    rw [rot1, rot1]
    rw [dif_pos (show (e.castSucc).val < m from by rw [hc]; exact e.isLt)]
    by_cases hlt : (e.succ).val < m
    · rw [dif_pos hlt]
      have := hpath ⟨e.val + 1, by rw [hs] at hlt; omega⟩
      exact this
    · rw [dif_neg hlt]
      have hem : e.val + 1 = m := by rw [hs] at hlt; omega
      have hg1 : g ⟨(e.castSucc).val + 1, by omega⟩ = g (Fin.last m) :=
        congrArg g (Fin.ext (by show (e.castSucc).val + 1 = m; omega))
      rw [hg1]
      intro hcon
      exact hclose (by rw [hcon, Equiv.apply_symm_apply])
  · rw [rot1, rot1, dif_neg (by simp),
      dif_pos (show (0 : Fin (m + 1)).val < m from by simp only [Fin.val_zero]; omega),
      Equiv.apply_symm_apply]
    have := hpath ⟨0, by omega⟩
    simpa using this

theorem unrot1_mem (hm : 1 ≤ m) (P : Equiv.Perm (Fin k)) {h : Fin (m + 1) → Fin k}
    (hh : h ∈ coverSet P m) : unrot1 P h ∈ coverSet P m := by
  simp only [coverSet, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
  obtain ⟨hpath, hclose⟩ := hh
  constructor
  · intro e
    rw [unrot1, unrot1]
    by_cases he0 : 0 < (e.castSucc).val
    · rw [dif_pos he0, dif_pos (show 0 < (e.succ).val from by simp)]
      have := hpath ⟨e.val - 1, by have := e.isLt; omega⟩
      have hcc : (⟨(e.castSucc).val - 1, by omega⟩ : Fin (m + 1))
          = (⟨e.val - 1, by have := e.isLt; omega⟩ : Fin m).castSucc := Fin.ext rfl
      have hss : (⟨(e.succ).val - 1, by omega⟩ : Fin (m + 1))
          = (⟨e.val - 1, by have := e.isLt; omega⟩ : Fin m).succ := by
        apply Fin.ext
        show (e.succ).val - 1 = e.val - 1 + 1
        have : (e.succ).val = e.val + 1 := rfl
        have h0 : 0 < e.val := he0
        omega
      rw [hcc, hss]
      exact this
    · rw [dif_neg he0, dif_pos (show 0 < (e.succ).val from by simp)]
      have he : e.val = 0 := by
        have : (e.castSucc).val = e.val := rfl
        omega
      have h1 : (⟨(e.succ).val - 1, by omega⟩ : Fin (m + 1)) = 0 := by
        apply Fin.ext
        show (e.succ).val - 1 = 0
        have : (e.succ).val = e.val + 1 := rfl
        omega
      rw [h1]
      exact hclose
  · rw [unrot1, unrot1, dif_pos (show 0 < (Fin.last m).val from by simp only [Fin.val_last]; omega),
      dif_neg (by simp)]
    intro hcon
    have hinj := P.injective hcon
    have := hpath ⟨m - 1, by omega⟩
    refine this ?_
    have hc : (⟨m - 1, by omega⟩ : Fin m).castSucc
        = (⟨(Fin.last m).val - 1, by omega⟩ : Fin (m+1)) :=
      Fin.ext (by simp)
    have hs : (⟨m - 1, by omega⟩ : Fin m).succ = Fin.last m := Fin.ext (by simp; omega)
    rw [hc, hs, hinj]

theorem unrot1_rot1 (P : Equiv.Perm (Fin k)) (g : Fin (m + 1) → Fin k) :
    unrot1 P (rot1 P g) = g := by
  funext s
  rw [unrot1]
  by_cases hs : 0 < s.val
  · rw [dif_pos hs, rot1, dif_pos (show s.val - 1 < m from by have := s.isLt; omega)]
    congr 1
    exact Fin.ext (by show s.val - 1 + 1 = s.val; omega)
  · rw [dif_neg hs, rot1, dif_neg (by simp), Equiv.apply_symm_apply]
    have hs0 : s.val = 0 := by omega
    congr 1
    exact Fin.ext (by simpa using hs0.symm)

theorem rot1_unrot1 (hm : 1 ≤ m) (P : Equiv.Perm (Fin k)) (h : Fin (m + 1) → Fin k) :
    rot1 P (unrot1 P h) = h := by
  funext t
  rw [rot1]
  by_cases ht : t.val < m
  · rw [dif_pos ht, unrot1, dif_pos (show 0 < t.val + 1 from by omega)]
    rfl
  · rw [dif_neg ht, unrot1, dif_neg (by simp), Equiv.symm_apply_apply]
    have htm : t.val = m := by have := t.isLt; omega
    congr 1
    exact Fin.ext (by simpa using htm.symm)

/-- **L4 (single step)**: the cover fibre at `j+1` has the same size as the fibre at `j`. -/
theorem card_cover_step (hm : 1 ≤ m) (P : Equiv.Perm (Fin k)) (j : Fin m) (d : Fin k) :
    ((coverSet P m).filter (fun g => g j.succ = d)).card
      = ((coverSet P m).filter (fun g => g j.castSucc = d)).card := by
  classical
  refine Finset.card_nbij' (rot1 P) (unrot1 P) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter] at hg ⊢
    refine ⟨rot1_mem hm P hg.1, ?_⟩
    have hjc : (j.castSucc).val = j.val := rfl
    rw [rot1, dif_pos (show (j.castSucc).val < m from j.isLt)]
    have : (⟨(j.castSucc).val + 1, by have := j.isLt; omega⟩ : Fin (m + 1)) = j.succ :=
      Fin.ext rfl
    rw [this]
    exact hg.2
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_filter] at hh ⊢
    refine ⟨unrot1_mem hm P hh.1, ?_⟩
    rw [unrot1, dif_pos (show 0 < (j.succ).val from by simp)]
    have : (⟨(j.succ).val - 1, by have := j.isLt; omega⟩ : Fin (m + 1)) = j.castSucc :=
      Fin.ext (by show (j.succ).val - 1 = j.val; rfl)
    rw [this]
    exact hh.2
  · intro g _
    exact unrot1_rot1 P g
  · intro h _
    exact rot1_unrot1 hm P h

/-- **L4**: every vertex sees the same cover fibre size. -/
theorem card_cover_vertex (hm : 1 ≤ m) (P : Equiv.Perm (Fin k)) (i : Fin (m + 1)) (d : Fin k) :
    ((coverSet P m).filter (fun g => g i = d)).card
      = ((coverSet P m).filter (fun g => g 0 = d)).card := by
  obtain ⟨v, hv⟩ : ∃ v, i.val = v := ⟨i.val, rfl⟩
  induction v generalizing i with
  | zero =>
    have : i = 0 := Fin.ext (by simpa using hv)
    rw [this]
  | succ v ih =>
    have hvm : v < m := by have := i.isLt; omega
    have hi : i = (⟨v, hvm⟩ : Fin m).succ := Fin.ext (by show i.val = v + 1; omega)
    rw [hi, card_cover_step hm P ⟨v, hvm⟩ d]
    exact ih (⟨v, hvm⟩ : Fin m).castSucc rfl

end Rotate

section Alternating

variable {m : ℕ}

/-- The alternating cover coloring attached to a moved label. -/
def altCol (P : Equiv.Perm (Fin k)) (m : ℕ) (c : Fin k) : Fin (m + 1) → Fin k :=
  fun j => if Even j.val then c else P c

theorem altCol_mem (hm : Even m) (P : Equiv.Perm (Fin k)) {c : Fin k} (hc : P c ≠ c) :
    altCol P m c ∈ coverSet P m := by
  simp only [coverSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro e
    have hc' : (e.castSucc).val = e.val := rfl
    have hs' : (e.succ).val = e.val + 1 := rfl
    simp only [altCol]
    by_cases hpar : Even e.val
    · rw [if_pos (by rw [hc']; exact hpar), if_neg (by rw [hs']; simp [Nat.even_add_one, hpar])]
      exact fun h => hc h.symm
    · rw [if_neg (by rw [hc']; exact hpar), if_pos (by rw [hs']; simp [Nat.even_add_one, hpar])]
      exact hc
  · simp only [altCol]
    rw [if_pos (show Even (Fin.last m).val from by simpa using hm), if_pos (by simp)]
    exact hc

/-- The alternating family: one coloring per moved label. -/
def altSet (P : Equiv.Perm (Fin k)) (m : ℕ) : Finset (Fin (m + 1) → Fin k) :=
  (Finset.univ.filter (fun c => P c ≠ c)).image (altCol P m)

theorem altCol_injOn (P : Equiv.Perm (Fin k)) (m : ℕ) :
    Set.InjOn (altCol P m) (Finset.univ.filter (fun c => P c ≠ c) : Finset (Fin k)) := by
  intro a _ b _ hab
  have := congrFun hab (0 : Fin (m + 1))
  rwa [altCol, altCol, if_pos (by simp), if_pos (by simp)] at this

theorem altSet_subset (hm : Even m) (P : Equiv.Perm (Fin k)) :
    altSet P m ⊆ coverSet P m := by
  intro g hg
  rw [altSet, Finset.mem_image] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  exact altCol_mem hm P (Finset.mem_filter.mp hc).2

/-- **L8**: the alternating family contributes exactly one coloring per moved label at every
vertex. -/
theorem card_alt_filter (_hm : Even m) (P : Equiv.Perm (Fin k)) (i : Fin (m + 1)) (d : Fin k) :
    ((altSet P m).filter (fun g => g i = d)).card = if P.symm d = d then 0 else 1 := by
  classical
  have hkey : (altSet P m).filter (fun g => g i = d)
      = ((Finset.univ.filter (fun c => P c ≠ c)).filter
          (fun c => altCol P m c i = d)).image (altCol P m) := by
    rw [altSet, Finset.filter_image]
  rw [hkey, Finset.card_image_of_injOn
    (Set.InjOn.mono (by intro x hx; exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter x
      (Finset.mem_coe.mp hx))) (altCol_injOn P m))]
  -- the surviving label is `d` at even indices and `P⁻¹ d` at odd ones
  set u : Fin k := if Even i.val then d else P.symm d with hu
  have hmem : ∀ c : Fin k, (c ∈ (Finset.univ.filter (fun c => P c ≠ c)).filter
      (fun c => altCol P m c i = d)) ↔ (P.symm d ≠ d ∧ c = u) := by
    intro c
    have halt : altCol P m c i = if Even i.val then c else P c := rfl
    rw [Finset.mem_filter, Finset.mem_filter, halt]
    simp only [Finset.mem_univ, true_and, hu]
    by_cases hpar : Even i.val
    · rw [if_pos hpar, if_pos hpar]
      constructor
      · rintro ⟨hc, rfl⟩
        exact ⟨fun h => hc ((Equiv.symm_apply_eq P).mp h).symm, rfl⟩
      · rintro ⟨hd, rfl⟩
        exact ⟨fun h => hd ((Equiv.symm_apply_eq P).mpr h.symm), rfl⟩
    · rw [if_neg hpar, if_neg hpar]
      constructor
      · rintro ⟨hc, rfl⟩
        rw [Equiv.symm_apply_apply]
        exact ⟨fun h => hc h.symm, rfl⟩
      · rintro ⟨hd, rfl⟩
        rw [Equiv.apply_symm_apply]
        exact ⟨fun h => hd h.symm, rfl⟩
  by_cases hfix : P.symm d = d
  · rw [if_pos hfix, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    exact fun c hc => (hmem c).mp hc |>.1 hfix
  · rw [if_neg hfix]
    refine Finset.card_eq_one.mpr ⟨u, ?_⟩
    ext c
    rw [hmem c, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨hfix, h⟩⟩

/-- **L9**: the balanced core of the cover has exactly `A` colorings at every label of every
vertex. -/
theorem card_balanced (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : Even m) (P : Equiv.Perm (Fin k))
    (i : Fin (m + 1)) (d : Fin k) :
    (((coverSet P m) \ (altSet P m)).filter (fun g => g i = d)).card = uniformA k (m + 1) := by
  classical
  have hsub : (altSet P m).filter (fun g => g i = d)
      ⊆ (coverSet P m).filter (fun g => g i = d) :=
    Finset.filter_subset_filter _ (altSet_subset hm P)
  have hsd : ((coverSet P m) \ (altSet P m)).filter (fun g => g i = d)
      = (coverSet P m).filter (fun g => g i = d) \ (altSet P m).filter (fun g => g i = d) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hsd, Finset.card_sdiff_of_subset hsub, card_cover_vertex hm1 P i d, card_cover_root,
    cover_diag_value hk hm P d, card_alt_filter hm P i d]
  by_cases hfix : P.symm d = d <;> simp [hfix]

end Alternating

section Transfer

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The labelling map carrying an index function to a colouring of `V`. -/
def labelOf {m k : ℕ} (ix : Fin (m + 1) ≃ V) (σ : Fin (m + 1) → Fin k → ℕ)
    (g : Fin (m + 1) → Fin k) : V → ℕ := fun v => σ (ix.symm v) (g (ix.symm v))

/-- **L10**: every cover coloring is a proper `L`-colouring. -/
theorem labelOf_mem_colorings {m k : ℕ} (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (L : ListAssignment V) (σ : Fin (m + 1) → Fin k → ℕ)
    (hσmem : ∀ i x, σ i x ∈ L (ix i)) (hσinj : ∀ i, Function.Injective (σ i))
    (hσmatch : ∀ (i : Fin (m + 1)) (h : i.val + 1 < m + 1) (x : Fin k),
      σ i x ∈ L (ix ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (P : Equiv.Perm (Fin k)) (dom : Finset (Fin k))
    (hdom : ∀ c, c ∈ dom ↔ σ 0 c ∈ L (ix (Fin.last m)))
    (hP : ∀ c ∈ dom, σ (Fin.last m) (P.symm c) = σ 0 c)
    {g : Fin (m + 1) → Fin k} (hg : g ∈ coverSet P m) :
    labelOf ix σ g ∈ G.colorings L := by
  classical
  simp only [coverSet, Finset.mem_filter, Finset.mem_univ, true_and] at hg
  obtain ⟨hpath, hclose⟩ := hg
  -- the factor entry is colour compatibility across a path edge (as in `rootedCol_eq_rootCount`)
  have hfac : ∀ (e : Fin m) (x y : Fin k),
      (offDiag k + diagInd (Finset.univ.filter
        (fun z => σ e.castSucc z ≠ σ e.succ z))) x y = 1 ↔ σ e.castSucc x ≠ σ e.succ y := by
    intro e x y
    have hlt : (Fin.castSucc e : Fin (m + 1)).val + 1 < m + 1 := by
      have := e.isLt; simp only [Fin.val_castSucc]; omega
    have hcast : (⟨(Fin.castSucc e : Fin (m + 1)).val + 1, hlt⟩ : Fin (m + 1)) = e.succ :=
      Fin.ext (by simp)
    refine factor_eq_one_iff (B := L (ix e.succ)) (fun i => hσmem e.succ i) (hσinj e.succ)
      (fun z hz => ?_) x y
    have h2 := hσmatch (Fin.castSucc e) hlt z (by rw [hcast]; exact hz)
    rwa [hcast] at h2
  have key : ∀ i j : Fin (m + 1), j = i + 1 → σ i (g i) ≠ σ j (g j) := by
    intro i j hij
    rcases fin_succ_cases hij with ⟨e, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine (hfac e _ _).mp ?_
      rw [factor_apply, if_neg (hpath e)]
    · intro hcon
      have hmem : σ 0 (g 0) ∈ L (ix (Fin.last m)) := hcon ▸ hσmem (Fin.last m) (g (Fin.last m))
      have hd : g 0 ∈ dom := (hdom (g 0)).mpr hmem
      have h2 : σ (Fin.last m) (P.symm (g 0)) = σ (Fin.last m) (g (Fin.last m)) := by
        rw [hP (g 0) hd, hcon]
      have h3 : P.symm (g 0) = g (Fin.last m) := hσinj (Fin.last m) h2
      exact hclose (by rw [← h3, Equiv.apply_symm_apply])
  rw [SimpleGraph.mem_colorings_iff]
  refine ⟨fun v => ?_, fun u v huv => ?_⟩
  · have := hσmem (ix.symm v) (g (ix.symm v))
    rwa [Equiv.apply_symm_apply] at this
  · have h1 : G.Adj (ix (ix.symm u)) (ix (ix.symm v)) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact huv
    rcases (hadj _ _).mp h1 with h | h
    · exact key _ _ h
    · exact (key _ _ h).symm

/-- **L11**: the labelling map is injective, so fibres transport. -/
theorem labelOf_injective {m k : ℕ} (ix : Fin (m + 1) ≃ V) (σ : Fin (m + 1) → Fin k → ℕ)
    (hσinj : ∀ i, Function.Injective (σ i)) : Function.Injective (labelOf ix σ) := by
  intro g₁ g₂ h
  funext i
  have hi := congrFun h (ix i)
  simp only [labelOf, Equiv.symm_apply_apply] at hi
  exact hσinj i hi

theorem card_image_fibre {m k : ℕ} (ix : Fin (m + 1) ≃ V) (σ : Fin (m + 1) → Fin k → ℕ)
    (hσinj : ∀ i, Function.Injective (σ i)) (S : Finset (Fin (m + 1) → Fin k))
    (v : V) {c : ℕ} {d : Fin k} (hd : σ (ix.symm v) d = c) :
    ((S.image (labelOf ix σ)).filter (fun f => f v = c)).card
      = (S.filter (fun g => g (ix.symm v) = d)).card := by
  classical
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (labelOf_injective ix σ hσinj)]
  congr 1
  apply Finset.filter_congr
  intro g _
  simp only [labelOf, ← hd]
  exact ⟨fun h => hσinj (ix.symm v) h, fun h => by rw [h]⟩

end Transfer

section Assembly

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **L12**: the cover model — the enumeration chain together with the completed closing
permutation. This is `exists_matrix_model`'s opening, with `σ` and the closing data exposed. -/
theorem exists_cover_model {m k : ℕ} (ix : Fin (m + 1) ≃ V)
    (L : ListAssignment V) (hL : IsNListAssignment L k) :
    ∃ (σ : Fin (m + 1) → Fin k → ℕ) (P : Equiv.Perm (Fin k)) (dom : Finset (Fin k)),
      (∀ i x, σ i x ∈ L (ix i)) ∧ (∀ i, Function.Injective (σ i)) ∧
      (∀ (i : Fin (m + 1)) (h : i.val + 1 < m + 1) (x : Fin k),
        σ i x ∈ L (ix ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x) ∧
      (∀ c, c ∈ dom ↔ σ 0 c ∈ L (ix (Fin.last m))) ∧
      (∀ c ∈ dom, σ (Fin.last m) (P.symm c) = σ 0 c) := by
  classical
  obtain ⟨σ, hσmem, hσinj, hσmatch⟩ := exists_enum_chain (by omega)
    (fun i : Fin (m + 1) => L (ix i)) (fun i => hL (ix i))
  set dom : Finset (Fin k) := Finset.univ.filter
    (fun c => σ 0 c ∈ L (ix (Fin.last m))) with hdom
  have hμex : ∀ c ∈ dom, ∃ x, σ (Fin.last m) x = σ 0 c := by
    intro c hc
    rw [hdom, Finset.mem_filter] at hc
    exact enum_surj (hL (ix (Fin.last m))) (hσmem (Fin.last m)) (hσinj (Fin.last m)) hc.2
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
  have hgex : ∀ a ∈ dom.image μ, ∃ c ∈ dom, μ c = a := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨c, hc, hca⟩ := ha
    exact ⟨c, hc, hca⟩
  set g : Fin k → Fin k := fun a => if ha : a ∈ dom.image μ then
      Classical.choose (hgex a ha) else a with hg
  have hgspec : ∀ a (ha : a ∈ dom.image μ),
      Classical.choose (hgex a ha) ∈ dom ∧ μ (Classical.choose (hgex a ha)) = a :=
    fun a ha => ⟨(Classical.choose_spec (hgex a ha)).1, (Classical.choose_spec (hgex a ha)).2⟩
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
  refine ⟨σ, P, dom, hσmem, hσinj, hσmatch, fun c => ?_, fun c hc => ?_⟩
  · rw [hdom, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ c, h⟩⟩
  · rw [hPsymm c hc]; exact hμspec c hc

/-- **UM-025, general list size**: on an odd cycle with `k`-lists (`k ≥ 2`) there is a family of
proper `L`-colourings using every colour of every list exactly `A = rootedCol G (constList V k)`
times.  Only `1 ≤ m` and `Even m` are used; `k = 3` is not special. -/
theorem exists_balanced_core_odd_gen {m k : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Odd (m + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L k) :
    ∃ S : Finset (V → ℕ), S ⊆ G.colorings L ∧
      ∀ v, ∀ c ∈ L v,
        (S.filter (fun f => f v = c)).card = rootedCol G (constList V k) (ix 0) 0 := by
  classical
  have hmeven : Even m := by
    rcases hpar with ⟨t, ht⟩
    exact ⟨t, by omega⟩
  obtain ⟨σ, P, dom, hσmem, hσinj, hσmatch, hdom, hP⟩ := exists_cover_model ix L hL
  refine ⟨(((coverSet P m) \ (altSet P m)).image (labelOf ix σ)), ?_, ?_⟩
  · rw [Finset.image_subset_iff]
    intro g hg
    exact labelOf_mem_colorings ix hadj L σ hσmem hσinj hσmatch P dom hdom hP
      (Finset.mem_sdiff.mp hg).1
  · intro v c hc
    obtain ⟨d, hd⟩ := enum_surj (hL (ix (ix.symm v))) (hσmem (ix.symm v)) (hσinj (ix.symm v))
      (show c ∈ L (ix (ix.symm v)) from by rw [Equiv.apply_symm_apply]; exact hc)
    rw [card_image_fibre ix σ hσinj _ v hd,
      card_balanced hk hm hmeven P (ix.symm v) d,
      rootedCol_constList_cycle (by omega) ix hadj]

/-- **UM-025**, the `k = 3` instance consumed by `cycle_gm_bound` (`Cacti/GMFinal.lean`): the
balanced core of an odd cycle. -/
theorem exists_balanced_core_odd {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Odd (m + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) :
    ∃ S : Finset (V → ℕ), S ⊆ G.colorings L ∧
      ∀ v, ∀ c ∈ L v,
        (S.filter (fun f => f v = c)).card = rootedCol G (constList V 3) (ix 0) 0 :=
  exists_balanced_core_odd_gen (by omega) (by omega) ix hadj hpar L hL


end Assembly

end ListColoring
