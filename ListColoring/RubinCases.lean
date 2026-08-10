/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.RubinStructure
import ListColoring.ThetaGen

/-!
# Rubin's theorem: the theta bridge, and steps 4–6

**Attribution.** Everything in this file serves the hard direction of **Rubin's theorem**
(A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West Coast
Conf. on Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congr. Numer. **26**,
Utilitas Math., Winnipeg, **1980**, 125–157, pp. 131–134). **Nothing here is new mathematics**;
the case analysis is Rubin's own, and everything else is mechanization.

## What this file adds

`ListColoring.RubinStructure` supplies Rubin's steps 1–3 and the existence of his connecting paths.
This file supplies the two remaining pieces.

* **The theta bridge.** The choosability results of `ListColoring.ThetaGen` are stated about the
  abstract graph `ListColoring.gtheta ks`, while Rubin's steps produce *walks*.
  `ListColoring.contains_gtheta_of_walks` converts `n` internally disjoint paths joining two
  branch vertices into `ListColoring.Contains G (gtheta ks)`, which
  `ListColoring.not_choosable_of_contains` then consumes. This is the analogue for thetas of the
  `getVert` bridge at the top of `ListColoring.RubinStructure`, and like it is pure mechanization.
* **Steps 4, 5 and 6.** Step 4 shows that `C₁ ∪ P₁` must be `θ_{2,2,2m}` and, using minimality of
  `C₁`, that `C₁` is a four-cycle. Step 6's case analysis on the ends of the second connecting
  path `P₂` then rules out any further edge.

## Three corrections to Rubin's published argument

All three were found by running his procedure over all `316,460` connected bipartite
minimum-degree-`≥ 2` non-cycle graphs on at most `8` vertices, and are recorded in
`ListColoring.RubinStructure`; this file respects them.

1. **Cases (i) and (ii) cannot occur** — each produces a cycle meeting `C₁` in at most one node,
   which his step 3 has already excluded. They are nevertheless discharged directly here, in
   `ListColoring.case_onP1`, which is cheaper than re-deriving the step-3 hypothesis.
2. **Case (v)'s sub-split is unnecessary, and without minimality of `P₁` it is wrong** — the arms
   `2, 2, 4, 2` contain no bad three-arm theta. `ListColoring.case_branches` uses Rubin's type `5`
   unconditionally instead: four arms of any lengths.
3. **Step 5's "`C₁` must be a `4`-cycle" needs minimality of `C₁`**, which enters
   `ListColoring.step4` through the hypothesis `hmin`.

## Main results

* `ListColoring.contains_gtheta_of_arms`, `ListColoring.contains_gtheta_of_walks` — the bridge
* `ListColoring.not_choosable_two_of_three_arms`, `ListColoring.not_choosable_two_of_four_arms` —
  Rubin's types `4` and `5`, stated over arm data
* `ListColoring.step4` — Rubin's steps 4 and 5: `C₁ ∪ P₁` is `θ_{2,2,2m}` and `C₁` is a four-cycle
* `ListColoring.case_onP1`, `ListColoring.case_interior`, `ListColoring.case_mixed`,
  `ListColoring.case_branches`, `ListColoring.case_middles` — Rubin's six cases (his (i) and (ii)
  merged into the first)
* `ListColoring.step56` — the case analysis assembled: no edge lies outside `C₁ ∪ P₁`
* `ListColoring.rubin_structure` — **the structural half of Rubin's theorem**: a connected,
  `2`-choosable graph of minimum degree `≥ 2` is an even cycle or `θ_{2,2,2m}`, stated as data
  about walks so that the isomorphism constructions can consume it
-/

namespace ListColoring

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Decoding the index layout of `ListColoring.gtheta` -/

/-- Which arm the interior index `x` of `Θ(k₁, …, k_n)` belongs to. Pure bookkeeping: the inverse
of the running-offset layout `ListColoring.gsize (ks.take i) + j`. -/
def gArmOf : List ℕ → ℕ → ℕ
  | [], _ => 0
  | k :: ks, x => if x < k - 1 then 0 else gArmOf ks (x - (k - 1)) + 1

/-- The position of the interior index `x` inside its own arm. -/
def gOffOf : List ℕ → ℕ → ℕ
  | [], x => x
  | k :: ks, x => if x < k - 1 then x else gOffOf ks (x - (k - 1))

/-- **Encoding round-trips**: the index `gsize (ks.take i) + j` decodes to arm `i`, offset `j`. -/
theorem gArmOf_gsize_take_add (ks : List ℕ) (i : ℕ) (hi : i < ks.length) (j : ℕ)
    (hj : j < ks[i] - 1) :
    gArmOf ks (gsize (ks.take i) + j) = i ∧ gOffOf ks (gsize (ks.take i) + j) = j := by
  induction ks generalizing i with
  | nil => simp at hi
  | cons k ks ih =>
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero] at hj
          simp only [List.take_zero, gsize_nil, Nat.zero_add, gArmOf, gOffOf, if_pos hj]
          exact ⟨trivial, trivial⟩
      | succ i =>
          have hi' : i < ks.length := by simpa using hi
          have hj' : j < ks[i] - 1 := by simpa using hj
          obtain ⟨h1, h2⟩ := ih i hi' hj'
          have hx : gsize ((k :: ks).take (i + 1)) + j = (k - 1) + (gsize (ks.take i) + j) := by
            simp only [List.take_succ_cons, gsize_cons]; omega
          have hnot : ¬ ((k - 1) + (gsize (ks.take i) + j) < k - 1) := by omega
          rw [hx]
          simp only [gArmOf, gOffOf, if_neg hnot,
            show (k - 1) + (gsize (ks.take i) + j) - (k - 1) = gsize (ks.take i) + j from by omega,
            h1, h2]
          exact ⟨trivial, trivial⟩

/-- **Decoding**: every interior index of `Θ(k₁, …, k_n)` sits at some offset inside some arm. -/
theorem gDecode (ks : List ℕ) (x : ℕ) (hx : x < gsize ks) :
    ∃ i, ∃ hi : i < ks.length, ∃ j, j < ks[i] - 1 ∧ gArmOf ks x = i ∧ gOffOf ks x = j ∧
      gsize (ks.take i) + j = x := by
  induction ks generalizing x with
  | nil => simp at hx
  | cons k ks ih =>
      by_cases h : x < k - 1
      · exact ⟨0, by simp, x, by simpa using h, by simp [gArmOf, if_pos h],
          by simp [gOffOf, if_pos h], by simp⟩
      · have hx' : x - (k - 1) < gsize ks := by simp only [gsize_cons] at hx; omega
        obtain ⟨i, hi, j, hj, h1, h2, h3⟩ := ih (x - (k - 1)) hx'
        refine ⟨i + 1, by simpa using hi, j, by simpa using hj, ?_, ?_, ?_⟩
        · simp only [gArmOf, if_neg h, h1]
        · simp only [gOffOf, if_neg h, h2]
        · simp only [List.take_succ_cons, gsize_cons]; omega

/-! ### Inverting the adjacency Boolean -/

/-- `ListColoring.armStepB`, read as a proposition. -/
theorem armStepB_iff (o m ps pt x y : ℕ) :
    armStepB o m ps pt x y = true ↔
      (m = 0 ∧ x = ps ∧ y = pt) ∨
      (m ≠ 0 ∧ ((x = ps ∧ y = o) ∨ (o ≤ x ∧ y = x + 1 ∧ y < o + m) ∨
        (x = o + m - 1 ∧ y = pt))) := by
  unfold armStepB
  split
  · simp_all
  · simp_all only [false_and, false_or, ne_eq, not_false_eq_true, true_and, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    tauto

/-- **Every edge of `Θ(k₁, …, k_n)` is a step along one of its arms.** The converse of
`ListColoring.gAdjAux_of_armStepB`. -/
theorem gAdjAux_iff (ks : List ℕ) (o ps pt x y : ℕ) :
    gAdjAux ks o ps pt x y = true ↔
      ∃ i, ∃ hi : i < ks.length,
        armStepB (o + gsize (ks.take i)) (ks[i] - 1) ps pt x y = true := by
  induction ks generalizing o with
  | nil => simp [gAdjAux]
  | cons k ks ih =>
      simp only [gAdjAux, Bool.or_eq_true, ih]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨0, by simp, by simpa using h⟩
        · refine ⟨i + 1, by simpa using hi, ?_⟩
          simp only [List.take_succ_cons, gsize_cons, List.getElem_cons_succ]
          rwa [show o + ((k - 1) + gsize (ks.take i)) = o + (k - 1) + gsize (ks.take i) from
            by omega]
      · rintro ⟨i, hi, h⟩
        cases i with
        | zero => exact Or.inl (by simpa using h)
        | succ i =>
            refine Or.inr ⟨i, by simpa using hi, ?_⟩
            simp only [List.take_succ_cons, gsize_cons, List.getElem_cons_succ] at h
            rwa [show o + (k - 1) + gsize (ks.take i) = o + ((k - 1) + gsize (ks.take i)) from
              by omega]

/-- **Every edge of `Θ(k₁, …, k_n)` is a step along one of its arms**, in the graph's own
adjacency. -/
theorem gAdjB_iff (ks : List ℕ) (x y : ℕ) :
    gAdjB ks x y = true ↔
      ∃ i, ∃ hi : i < ks.length,
        armStepB (gsize (ks.take i)) (ks[i] - 1) (gsize ks) (gsize ks + 1) x y = true := by
  simp only [gAdjB, gAdjAux_iff, Nat.zero_add]

/-! ### C1 — a generalized theta from arm data

Rubin's steps 4–6 produce **walks**, while the choosability results of `ListColoring.ThetaGen` are
stated about the abstract graph `ListColoring.gtheta ks`. This section is the bridge, and it is
**mechanization only**: it re-indexes `n` internally disjoint paths joining two vertices onto the
layout `Fin (gsize ks + 2)` that `ListColoring.gtheta` uses. It is the exact analogue of the
`getVert` bridge at the top of `ListColoring.RubinStructure`. -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **A generalized theta from arm data.** If `A i 0, A i 1, …, A i kᵢ` is a walk from `s` to `t`
for each `i < n`, the walks are internally disjoint from each other and from `{s, t}`, and `s ≠ t`,
then `G` contains `Θ(k₁, …, k_n)`.

Mechanization, not mathematics: the content is the re-indexing of the arms onto
`Fin (gsize ks + 2)`. -/
theorem contains_gtheta_of_arms {s t : V} {ks : List ℕ} (A : ℕ → ℕ → V) (hst : s ≠ t)
    (hk : ∀ i, ∀ hi : i < ks.length, 1 ≤ ks[i])
    (hstart : ∀ i, i < ks.length → A i 0 = s)
    (hend : ∀ i, ∀ hi : i < ks.length, A i ks[i] = t)
    (hadj : ∀ i, ∀ hi : i < ks.length, ∀ j, j < ks[i] → G.Adj (A i j) (A i (j + 1)))
    (hne : ∀ i, ∀ hi : i < ks.length, ∀ j, 0 < j → j < ks[i] → A i j ≠ s ∧ A i j ≠ t)
    (hinj : ∀ i, ∀ hi : i < ks.length, ∀ i', ∀ hi' : i' < ks.length, ∀ j j',
      0 < j → j < ks[i] → 0 < j' → j' < ks[i'] → A i j = A i' j' → i = i' ∧ j = j') :
    Contains G (gtheta ks) := by
  classical
  set f : GTV ks → V := fun v =>
    if _ : v.val < gsize ks then A (gArmOf ks v.val) (gOffOf ks v.val + 1)
    else if v.val = gsize ks then s else t with hfdef
  -- the value of `f` at an interior index, at the two branch indices
  have hfint : ∀ (i : ℕ) (hi : i < ks.length) (j : ℕ), j < ks[i] - 1 →
      ∀ v : GTV ks, v.val = gsize (ks.take i) + j → f v = A i (j + 1) := by
    intro i hi j hj v hv
    have hle := gsize_take_add_le ks i hi
    have hlt : v.val < gsize ks := by omega
    obtain ⟨e1, e2⟩ := gArmOf_gsize_take_add ks i hi j hj
    simp only [hfdef, dif_pos hlt, hv, e1, e2]
  have hfs : ∀ v : GTV ks, v.val = gsize ks → f v = s := by
    intro v hv
    have h1 : ¬ (v.val < gsize ks) := by omega
    simp only [hfdef, dif_neg h1, if_pos hv]
  have hft : ∀ v : GTV ks, v.val = gsize ks + 1 → f v = t := by
    intro v hv
    have h1 : ¬ (v.val < gsize ks) := by omega
    have h2 : ¬ (v.val = gsize ks) := by omega
    simp only [hfdef, dif_neg h1, if_neg h2]
  -- every vertex is either interior, in which case its value is an interior arm vertex, or a
  -- branch vertex
  have hcases : ∀ v : GTV ks, (∃ i, ∃ hi : i < ks.length, ∃ j, 0 < j ∧ j < ks[i] ∧ f v = A i j ∧
      v.val = gsize (ks.take i) + (j - 1)) ∨
      (f v = s ∧ v.val = gsize ks) ∨ (f v = t ∧ v.val = gsize ks + 1) := by
    intro v
    by_cases hlt : v.val < gsize ks
    · obtain ⟨i, hi, j, hj, _, _, hsum⟩ := gDecode ks v.val hlt
      have hk1 := hk i hi
      exact Or.inl ⟨i, hi, j + 1, by omega, by omega, hfint i hi j hj v hsum.symm, by omega⟩
    · have := v.isLt
      rcases (by omega : v.val = gsize ks ∨ v.val = gsize ks + 1) with h | h
      · exact Or.inr (Or.inl ⟨hfs v h, h⟩)
      · exact Or.inr (Or.inr ⟨hft v h, h⟩)
  refine ⟨f, ?_, ?_⟩
  · -- injectivity
    intro v w hvw
    rcases hcases v with ⟨i, hi, j, hj0, hjk, hfv, hvu⟩ | ⟨hfv, hv⟩ | ⟨hfv, hv⟩ <;>
      rcases hcases w with ⟨i', hi', j', hj0', hjk', hfw, hwu⟩ | ⟨hfw, hw⟩ | ⟨hfw, hw⟩
    · obtain ⟨rfl, rfl⟩ := hinj i hi i' hi' j j' hj0 hjk hj0' hjk' (hfv.symm.trans (hvw.trans hfw))
      exact Fin.ext (by omega)
    · exact absurd (hfv.symm.trans (hvw.trans hfw)) (hne i hi j hj0 hjk).1
    · exact absurd (hfv.symm.trans (hvw.trans hfw)) (hne i hi j hj0 hjk).2
    · exact absurd (hfw.symm.trans (hvw.symm.trans hfv)) (hne i' hi' j' hj0' hjk').1
    · exact Fin.ext (hv.trans hw.symm)
    · exact absurd (hfv.symm.trans (hvw.trans hfw)) hst
    · exact absurd (hfw.symm.trans (hvw.symm.trans hfv)) (hne i' hi' j' hj0' hjk').2
    · exact absurd (hfw.symm.trans (hvw.symm.trans hfv)) hst
    · exact Fin.ext (hv.trans hw.symm)
  · -- adjacency
    have key : ∀ a b : GTV ks, gAdjB ks a.val b.val = true → G.Adj (f a) (f b) := by
      intro a b hab
      obtain ⟨i, hi, hstep⟩ := (gAdjB_iff ks a.val b.val).mp hab
      have hk1 := hk i hi
      have hle := gsize_take_add_le ks i hi
      rcases (armStepB_iff _ _ _ _ _ _).mp hstep with ⟨hm, ha, hb⟩ | ⟨hm, hrest⟩
      · -- an arm of length one: the single edge joining the two branch vertices
        have h1 : ks[i] = 1 := by omega
        have h := hadj i hi 0 (by omega)
        rw [hstart i hi] at h
        have h1' : A i 1 = t := h1 ▸ hend i hi
        rw [h1'] at h
        rw [hfs a ha, hft b hb]
        exact h
      · rcases hrest with ⟨ha, hb⟩ | ⟨hax, hby, hbo⟩ | ⟨ha, hb⟩
        · -- the first interior vertex of the arm
          have h := hadj i hi 0 (by omega)
          rw [hstart i hi] at h
          rw [hfs a ha, hfint i hi 0 (by omega) b (by omega)]
          exact h
        · -- a step inside the arm
          rw [hfint i hi (a.val - gsize (ks.take i)) (by omega) a (by omega),
            hfint i hi (a.val - gsize (ks.take i) + 1) (by omega) b (by omega)]
          exact hadj i hi _ (by omega)
        · -- the last interior vertex of the arm
          have e1 : ks[i] - 1 + 1 = ks[i] := by omega
          have h := hadj i hi (ks[i] - 1) (by omega)
          rw [e1, hend i hi] at h
          have e2 : ks[i] - 1 - 1 + 1 = ks[i] - 1 := by omega
          rw [hft b hb, hfint i hi (ks[i] - 1 - 1) (by omega) a (by omega), e2]
          exact h
    intro a b hadjt
    rcases hadjt.2 with h | h
    · exact key a b h
    · exact (key b a h).symm

/-! ### Arms, packaged

Rubin's steps 4–6 always produce their thetas as a handful of named arms, so the arm hypotheses
of `ListColoring.contains_gtheta_of_arms` are packaged here as two predicates. Bookkeeping only. -/

/-- `IsArm G s t P k` says that `P 0, P 1, …, P k` is a path in `G` from `s` to `t` of length
`k ≥ 1` that repeats no interior vertex and whose interior avoids `s` and `t`. -/
def IsArm (G : SimpleGraph V) (s t : V) (P : ℕ → V) (k : ℕ) : Prop :=
  1 ≤ k ∧ P 0 = s ∧ P k = t ∧ (∀ j, j < k → G.Adj (P j) (P (j + 1))) ∧
    (∀ j, 0 < j → j < k → P j ≠ s ∧ P j ≠ t) ∧
    (∀ j j', 0 < j → j < k → 0 < j' → j' < k → P j = P j' → j = j')

/-- Two arms are internally disjoint. -/
def ArmsDisj (P : ℕ → V) (k : ℕ) (Q : ℕ → V) (l : ℕ) : Prop :=
  ∀ j j', 0 < j → j < k → 0 < j' → j' < l → P j ≠ Q j'

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Internal disjointness of two arms is symmetric. -/
theorem ArmsDisj.symm {P Q : ℕ → V} {k l : ℕ} (h : ArmsDisj P k Q l) : ArmsDisj Q l P k :=
  fun j j' hj hjk hj' hj'k e => h j' j hj' hj'k hj hjk e.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- `ListColoring.contains_gtheta_of_arms` with its hypotheses packaged as
`ListColoring.IsArm` and `ListColoring.ArmsDisj`. -/
theorem contains_gtheta_of_armFam {s t : V} {ks : List ℕ} (Arm : ℕ → ℕ → V) (hst : s ≠ t)
    (harm : ∀ i, ∀ hi : i < ks.length, IsArm G s t (Arm i) ks[i])
    (hdisj : ∀ i, ∀ hi : i < ks.length, ∀ i', ∀ hi' : i' < ks.length, i ≠ i' →
      ArmsDisj (Arm i) ks[i] (Arm i') ks[i']) :
    Contains G (gtheta ks) := by
  refine contains_gtheta_of_arms Arm hst (fun i hi => (harm i hi).1)
    (fun i hi => (harm i hi).2.1) (fun i hi => (harm i hi).2.2.1)
    (fun i hi => (harm i hi).2.2.2.1) (fun i hi => (harm i hi).2.2.2.2.1) ?_
  intro i hi i' hi' j j' hj0 hjk hj0' hjk' he
  by_cases hii : i = i'
  · subst hii
    exact ⟨rfl, (harm i hi).2.2.2.2.2 j j' hj0 hjk hj0' hjk' he⟩
  · exact absurd he (hdisj i hi i' hi' hii j j' hj0 hjk hj0' hjk')

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Three internally disjoint arms give a three-arm generalized theta. -/
theorem contains_gtheta_three {s t : V} {a b c : ℕ} {P Q R : ℕ → V} (hst : s ≠ t)
    (hP : IsArm G s t P a) (hQ : IsArm G s t Q b) (hR : IsArm G s t R c)
    (hPQ : ArmsDisj P a Q b) (hPR : ArmsDisj P a R c) (hQR : ArmsDisj Q b R c) :
    Contains G (gtheta [a, b, c]) := by
  refine contains_gtheta_of_armFam (fun i => if i = 0 then P else if i = 1 then Q else R) hst
    ?_ ?_
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have h1 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases h1 with rfl | rfl | rfl
    · simpa using hP
    · simpa using hQ
    · simpa using hR
  · intro i hi i' hi' hii
    simp only [List.length_cons, List.length_nil] at hi hi'
    have h1 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have h2 : i' = 0 ∨ i' = 1 ∨ i' = 2 := by omega
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, reduceIte] <;>
      first
        | exact absurd rfl hii
        | exact hPQ | exact hPR | exact hQR
        | exact hPQ.symm | exact hPR.symm | exact hQR.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Four internally disjoint arms give a four-arm generalized theta. -/
theorem contains_gtheta_four {s t : V} {a b c d : ℕ} {P Q R S : ℕ → V} (hst : s ≠ t)
    (hP : IsArm G s t P a) (hQ : IsArm G s t Q b) (hR : IsArm G s t R c) (hS : IsArm G s t S d)
    (hPQ : ArmsDisj P a Q b) (hPR : ArmsDisj P a R c) (hPS : ArmsDisj P a S d)
    (hQR : ArmsDisj Q b R c) (hQS : ArmsDisj Q b S d) (hRS : ArmsDisj R c S d) :
    Contains G (gtheta [a, b, c, d]) := by
  refine contains_gtheta_of_armFam
    (fun i => if i = 0 then P else if i = 1 then Q else if i = 2 then R else S) hst ?_ ?_
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h1 with rfl | rfl | rfl | rfl
    · simpa using hP
    · simpa using hQ
    · simpa using hR
    · simpa using hS
  · intro i hi i' hi' hii
    simp only [List.length_cons, List.length_nil] at hi hi'
    have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have h2 : i' = 0 ∨ i' = 1 ∨ i' = 2 ∨ i' = 3 := by omega
    rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, reduceIte] <;>
      first
        | exact absurd rfl hii
        | exact hPQ | exact hPR | exact hPS | exact hQR | exact hQS | exact hRS
        | exact hPQ.symm | exact hPR.symm | exact hPS.symm
        | exact hQR.symm | exact hQS.symm | exact hRS.symm

/-! ### Arms from Mathlib walks

Steps 4–6 hold their arms sometimes as index sequences and sometimes as `SimpleGraph.Walk`s; the
two converters below move a walk into arm form. Mechanization only. -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **A path walk is an arm**, indexed by `ListColoring.getVert`. -/
theorem isArm_of_walk {s t : V} (p : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t) :
    IsArm G s t p.getVert p.length := by
  have hinj := hp.getVert_injOn
  refine ⟨?_, p.getVert_zero, p.getVert_length, fun j hj => p.adj_getVert_succ hj, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos p.length with h | h
    · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h) hst
    · exact h
  · intro j hj0 hjl
    constructor
    · intro he
      have : j = 0 := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) (by rw [he, p.getVert_zero])
      omega
    · intro he
      have : j = p.length := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) (by rw [he, p.getVert_length])
      omega
  · intro j j' _ hjl _ hj'l he
    exact hinj (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) he

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **Two path walks meeting only at their ends give internally disjoint arms.** -/
theorem armsDisj_of_walks {s t : V} (p q : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t)
    (h : ∀ x ∈ p.support, x ∈ q.support → x = s ∨ x = t) :
    ArmsDisj p.getVert p.length q.getVert q.length := by
  intro j j' hj0 hjl hj0' hj'l he
  have hmem : p.getVert j ∈ q.support := he ▸ q.getVert_mem_support j'
  rcases h _ (p.getVert_mem_support j) hmem with hs | ht
  · exact (isArm_of_walk p hp hst).2.2.2.2.1 j hj0 hjl |>.1 hs
  · exact (isArm_of_walk p hp hst).2.2.2.2.1 j hj0 hjl |>.2 ht

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **C1, in walk form.** Two branch vertices `s ≠ t` joined by `n` pairwise internally disjoint
paths of lengths `k₁, …, k_n` give a copy of `Θ(k₁, …, k_n)` inside `G`.

This is the bridge Rubin's steps 4–6 need in order to feed `ListColoring.choosable_two_gtheta_iff`
and `ListColoring.not_choosable_two_gtheta_of_four`, which speak about the abstract graph
`ListColoring.gtheta ks`. It is the analogue for thetas of the `getVert` bridge at the top of
`ListColoring.RubinStructure`, and like it is **pure mechanization**: no mathematics happens here,
only a change of encoding. -/
theorem contains_gtheta_of_walks {s t : V} {ks : List ℕ} (p : ℕ → G.Walk s t) (hst : s ≠ t)
    (hlen : ∀ i, ∀ hi : i < ks.length, (p i).length = ks[i])
    (hp : ∀ i, i < ks.length → (p i).IsPath)
    (hdisj : ∀ i, i < ks.length → ∀ i', i' < ks.length → i ≠ i' →
      ∀ x ∈ (p i).support, x ∈ (p i').support → x = s ∨ x = t) :
    Contains G (gtheta ks) := by
  refine contains_gtheta_of_armFam (fun i => (p i).getVert) hst (fun i hi => ?_)
    (fun i hi i' hi' hii => ?_)
  · exact hlen i hi ▸ isArm_of_walk (p i) (hp i hi) hst
  · exact hlen i hi ▸ hlen i' hi' ▸
      armsDisj_of_walks (p i) (p i') (hp i hi) hst (hdisj i hi i' hi' hii)


/-! ### The two arcs of a cycle

Rubin's `C₁ ∪ P₁` is a theta whose two short arms are the arcs into which `P₁`'s endpoints cut
`C₁`. Mathlib presents `C₁` as a `SimpleGraph.Walk`, so the arcs have to be read off it; rotating
the cycle to start at one endpoint keeps every index inside `[0, length]` and makes
`SimpleGraph.Walk.IsCycle.getVert_injOn'` directly applicable. Mechanization only. -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A step of a walk is an edge of it. -/
theorem getVert_mem_edges {x y : V} (p : G.Walk x y) : ∀ {i : ℕ}, i < p.length →
    s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
  induction p with
  | nil => intro i hi; simp at hi
  | @cons u v w h q ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ i =>
          simp only [SimpleGraph.Walk.length_cons] at hi
          simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.edges_cons,
            List.mem_cons]
          exact Or.inr (ih (by omega))

omit [Fintype V] [DecidableRel G.Adj] in
/-- **The two arcs of a cycle between two of its vertices.** They are internally disjoint arms
from `a` to `b`, their lengths add up to the length of the cycle, their vertices and edges are
vertices and edges of the cycle, and together they exhaust its vertices. -/
theorem exists_arcs_of_cycle {v : V} {c : G.Walk v v} (hc : c.IsCycle) {a b : V}
    (ha : a ∈ c.support) (hb : b ∈ c.support) (hab : a ≠ b) :
    ∃ (A B : ℕ → V) (α β : ℕ), 1 ≤ α ∧ 1 ≤ β ∧ α + β = c.length ∧
      IsArm G a b A α ∧ IsArm G a b B β ∧ ArmsDisj A α B β ∧
      (∀ t, t ≤ α → A t ∈ c.support) ∧ (∀ t, t ≤ β → B t ∈ c.support) ∧
      (∀ t, t < α → s(A t, A (t + 1)) ∈ c.edges) ∧
      (∀ t, t < β → s(B t, B (t + 1)) ∈ c.edges) ∧
      (∀ x, x ∈ c.support → (∃ t, t ≤ α ∧ A t = x) ∨ (∃ t, t ≤ β ∧ B t = x)) := by
  classical
  set c' : G.Walk a a := c.rotate a ha with hc'def
  have hc' : c'.IsCycle := (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hlen : c'.length = c.length := SimpleGraph.Walk.length_rotate c a ha
  have hmem : ∀ x : V, x ∈ c'.support ↔ x ∈ c.support := fun x =>
    SimpleGraph.Walk.mem_support_rotate_iff c a ha
  have hedg : ∀ e : Sym2 V, e ∈ c'.edges ↔ e ∈ c.edges := fun _ =>
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  set L : ℕ := c'.length with hLdef
  have h3 : 3 ≤ L := hc'.three_le_length
  have hinj : Set.InjOn c'.getVert {i | i ≤ L - 1} := hc'.getVert_injOn'
  have h0 : c'.getVert 0 = a := c'.getVert_zero
  have hLa : c'.getVert L = a := c'.getVert_length
  obtain ⟨j, hjget, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((hmem b).mpr hb)
  have hj0 : j ≠ 0 := by rintro rfl; exact hab (h0.symm.trans hjget)
  have hjL : j ≠ L := by rintro rfl; exact hab (hLa.symm.trans hjget)
  have hjlt : j < L := lt_of_le_of_ne hjle hjL
  have hj1 : 1 ≤ j := by omega
  refine ⟨c'.getVert, fun t => c'.getVert (L - t), j, L - j, hj1, by omega, by omega, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the arc `a → b` running forwards
    refine ⟨hj1, h0, hjget, fun t ht => c'.adj_getVert_succ (by omega), ?_, ?_⟩
    · intro t ht0 htj
      refine ⟨fun he => ?_, fun he => ?_⟩
      · have : t = 0 := hinj (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) (by rw [he, h0])
        omega
      · have : t = j := hinj (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) (by rw [he, ← hjget])
        omega
    · intro t t' _ htj _ ht'j he
      exact hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) he
  · -- the arc `a → b` running backwards
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · show c'.getVert (L - 0) = a
      rw [Nat.sub_zero]; exact hLa
    · show c'.getVert (L - (L - j)) = b
      rw [show L - (L - j) = j from by omega]; exact hjget
    · intro t ht
      show G.Adj (c'.getVert (L - t)) (c'.getVert (L - (t + 1)))
      have hstep := c'.adj_getVert_succ (i := L - t - 1) (by omega)
      rw [show L - t - 1 + 1 = L - t from by omega] at hstep
      rw [show L - (t + 1) = L - t - 1 from by omega]
      exact hstep.symm
    · intro t ht0 htb
      show c'.getVert (L - t) ≠ a ∧ c'.getVert (L - t) ≠ b
      refine ⟨fun he => ?_, fun he => ?_⟩
      · have : L - t = 0 := hinj (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) (by rw [he, h0])
        omega
      · have : L - t = j := hinj (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) (by rw [he, ← hjget])
        omega
    · intro t t' _ htb _ ht'b he
      have he' : c'.getVert (L - t) = c'.getVert (L - t') := he
      have : L - t = L - t' := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) he'
      omega
  · -- the two arcs are internally disjoint
    intro t t' ht0 htj ht0' ht'b he
    have he' : c'.getVert t = c'.getVert (L - t') := he
    have : t = L - t' := hinj (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he'
    omega
  · exact fun t _ => (hmem _).mp (c'.getVert_mem_support t)
  · exact fun t _ => (hmem _).mp (c'.getVert_mem_support (L - t))
  · exact fun t ht => (hedg _).mp (getVert_mem_edges c' (by omega))
  · intro t ht
    show s(c'.getVert (L - t), c'.getVert (L - (t + 1))) ∈ c.edges
    have hstep := getVert_mem_edges c' (i := L - t - 1) (by omega)
    rw [show L - t - 1 + 1 = L - t from by omega] at hstep
    rw [show L - (t + 1) = L - t - 1 from by omega, Sym2.eq_swap]
    exact (hedg _).mp hstep
  · intro x hx
    obtain ⟨n, hn, hnL⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ((hmem x).mpr hx)
    rcases (by omega : n ≤ j ∨ j < n) with h | h
    · exact Or.inl ⟨n, h, hn⟩
    · refine Or.inr ⟨L - n, by omega, ?_⟩
      show c'.getVert (L - (L - n)) = x
      rw [show L - (L - n) = n from by omega]; exact hn

/-! ### The two obstructions Rubin's cases produce

Every three-arm theta the six cases produce has an arm of length `1`, so it is never
`θ_{2,2,2m}`; and the four-arm one is Rubin's type `5` whatever its arm lengths. -/

set_option maxHeartbeats 1000000 in
/-- **A three-arm theta whose shape is not `2, 2, 2m` is not `2`-choosable** — Rubin's type `4`.
The arms may be given in any order: the sorting `ListColoring.ValidArms` asks for is done here.
`hxy`, `hxz`, `hyz` say that at most one arm has length `1`, without which the three arms would
not span a simple graph.

Due to A. L. Rubin (Erdős–Rubin–Taylor 1980, p. 133); the classification it quotes is
`ListColoring.choosable_two_gtheta_iff`. -/
theorem not_choosable_two_of_three_arms {s t : V} {x y z : ℕ} {P Q R : ℕ → V} (hst : s ≠ t)
    (hP : IsArm G s t P x) (hQ : IsArm G s t Q y) (hR : IsArm G s t R z)
    (hPQ : ArmsDisj P x Q y) (hPR : ArmsDisj P x R z) (hQR : ArmsDisj Q y R z)
    (hxy : ¬ (x = 1 ∧ y = 1)) (hxz : ¬ (x = 1 ∧ z = 1)) (hyz : ¬ (y = 1 ∧ z = 1))
    (hgood : ¬ ((x = 2 ∧ y = 2 ∧ Even z) ∨ (x = 2 ∧ z = 2 ∧ Even y) ∨
      (y = 2 ∧ z = 2 ∧ Even x))) :
    ¬ G.Choosable 2 := by
  have hx1 := hP.1
  have hy1 := hQ.1
  have hz1 := hR.1
  -- one application of the classification, for whichever order turns out to be the sorted one
  have main : ∀ (u₁ u₂ u₃ : ℕ) (P₁ P₂ P₃ : ℕ → V), IsArm G s t P₁ u₁ → IsArm G s t P₂ u₂ →
      IsArm G s t P₃ u₃ → ArmsDisj P₁ u₁ P₂ u₂ → ArmsDisj P₁ u₁ P₃ u₃ →
      ArmsDisj P₂ u₂ P₃ u₃ → u₁ ≤ u₂ → u₂ ≤ u₃ → 2 ≤ u₂ →
      ¬ (u₁ = 2 ∧ u₂ = 2 ∧ Even u₃) → ¬ G.Choosable 2 := by
    intro u₁ u₂ u₃ P₁ P₂ P₃ h1 h2 h3 h12 h13 h23 o1 o2 hu2 hbad
    refine not_choosable_of_contains (K := gtheta [u₁, u₂, u₃]) ?_
      (contains_gtheta_three hst h1 h2 h3 h12 h13 h23)
    intro hch
    obtain ⟨m, hm, he⟩ := (choosable_two_gtheta_iff
      (validArms_triple h1.1 o1 o2 hu2)).mp hch
    simp only [List.cons.injEq, and_true] at he
    exact hbad ⟨he.1, he.2.1, ⟨m, by omega⟩⟩
  -- the six orders
  rcases le_total x y with h1 | h1 <;> rcases le_total y z with h2 | h2 <;>
    rcases le_total x z with h3 | h3
  · exact main x y z P Q R hP hQ hR hPQ hPR hQR h1 h2 (by omega)
      (fun h => hgood (Or.inl h))
  · exact main x y z P Q R hP hQ hR hPQ hPR hQR h1 h2 (by omega)
      (fun h => hgood (Or.inl h))
  · exact main x z y P R Q hP hR hQ hPR hPQ hQR.symm h3 h2 (by omega)
      (fun h => hgood (Or.inr (Or.inl h)))
  · exact main z x y R P Q hR hP hQ hPR.symm hQR.symm hPQ h3 h1 (by omega)
      (fun h => hgood (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)))
  · exact main y x z Q P R hQ hP hR hPQ.symm hQR hPR h1 h3 (by omega)
      (fun h => hgood (Or.inl ⟨h.2.1, h.1, h.2.2⟩))
  · exact main y z x Q R P hQ hR hP hQR hPQ.symm hPR.symm h2 h3 (by omega)
      (fun h => hgood (Or.inr (Or.inr h)))
  · exact main y z x Q R P hQ hR hP hQR hPQ.symm hPR.symm (by omega) (by omega) (by omega)
      (fun h => hgood (Or.inr (Or.inr h)))
  · exact main z y x R Q P hR hQ hP hQR.symm hPR.symm hPQ.symm h2 h1 (by omega)
      (fun h => hgood (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩)))

/-- **A theta with an arm of length one is not `2`-choosable** — Rubin's type `4`, in the shape
his cases (iii), (iv) and (vi) produce it. Its arms are `1, b, c` with `b, c ≥ 2`, so its sorted
shape starts with `1` and is never `2, 2, 2m`. -/
theorem not_choosable_two_of_arm_one {s t : V} {b c : ℕ} {P Q R : ℕ → V} (hst : s ≠ t)
    (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hP : IsArm G s t P 1) (hQ : IsArm G s t Q b) (hR : IsArm G s t R c)
    (hPQ : ArmsDisj P 1 Q b) (hPR : ArmsDisj P 1 R c) (hQR : ArmsDisj Q b R c) :
    ¬ G.Choosable 2 :=
  not_choosable_two_of_three_arms hst hP hQ hR hPQ hPR hQR (by omega) (by omega) (by omega)
    (by rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, -, h⟩) <;> simp at h)

/-- **A generalized theta on four arms is not `2`-choosable** — Rubin's type `5`, in arm form.
The first arm may have length `1`; the other three must be longer, or the graph would not be
simple.

Due to A. L. Rubin (Erdős–Rubin–Taylor 1980, p. 133); the underlying result is
`ListColoring.not_choosable_two_gtheta_of_four`. -/
theorem not_choosable_two_of_four_arms {s t : V} {a b c d : ℕ} {P Q R S : ℕ → V} (hst : s ≠ t)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hP : IsArm G s t P a) (hQ : IsArm G s t Q b) (hR : IsArm G s t R c) (hS : IsArm G s t S d)
    (hPQ : ArmsDisj P a Q b) (hPR : ArmsDisj P a R c) (hPS : ArmsDisj P a S d)
    (hQR : ArmsDisj Q b R c) (hQS : ArmsDisj Q b S d) (hRS : ArmsDisj R c S d) :
    ¬ G.Choosable 2 := by
  refine not_choosable_of_contains (K := gtheta [a, b, c, d]) ?_
    (contains_gtheta_four hst hP hQ hR hS hPQ hPR hPS hQR hQS hRS)
  refine not_choosable_two_gtheta_of_four (by simp) (by simpa using hP.1) ?_
  intro i hi hi1
  simp only [List.length_cons, List.length_nil] at hi
  have h1 : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h1 with rfl | rfl | rfl <;> simpa using ‹_›


/-! ### Rubin's step 4

> Otherwise, let `P₁` be a shortest path which is edge-disjoint from `C₁` and which joins two
> distinct nodes of `C₁`. … If `C₁ ∪ P₁` is not in `T`, then we are in case (4.) and are done.

`C₁ ∪ P₁` is the theta whose arms are the two arcs of `C₁` and `P₁` itself, so
`ListColoring.not_choosable_two_of_three_arms` disposes of every shape but `θ_{2,2,2m}`; what is
left is to see that the two arcs are then the *short* arms, which is where minimality of `C₁`
enters (see the note on step 5 in `ListColoring.RubinStructure`). -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **Four vertices in a square carry a cycle of length four.** -/
theorem exists_isCycle_four {a x b y : V} (h1 : G.Adj a x) (h2 : G.Adj x b) (h3 : G.Adj b y)
    (h4 : G.Adj y a) (hab : a ≠ b) (hxy : x ≠ y) :
    ∃ d : G.Walk a a, d.IsCycle ∧ d.length = 4 := by
  refine ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3
    (SimpleGraph.Walk.cons h4 SimpleGraph.Walk.nil))), ?_, by simp⟩
  have e1 := h1.ne
  have e2 := h2.ne
  have e3 := h3.ne
  have e4 := h4.ne
  simp only [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil, List.tail_cons, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, or_false, ne_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, not_or, and_true, reduceCtorEq]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp_all <;> tauto

/-- **Rubin's step 4.** Let `C₁` be a shortest cycle of a `2`-choosable graph and `P₁` a path
joining two distinct vertices of `C₁`, internally disjoint from it and edge-disjoint from it.
Then `C₁` is a four-cycle and `P₁` has even length at least `2`; that is, `C₁ ∪ P₁` is
`θ_{2,2,2m}` and its two branch vertices are the ends of `P₁`.

Due to A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Congr.
Numer. **26** (1980), 125–157, p. 132 (steps 4 and 5). Rubin's step 5 asserts that `C₁` is a
`4`-cycle; the argument for it needs minimality of `C₁`, which is used here through `hmin`. -/
theorem step4 (hch : G.Choosable 2)
    {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    (hmin : ∀ (z : V) (d : G.Walk z z), d.IsCycle → c.length ≤ d.length)
    {a b : V} {p : G.Walk a b} (ha : a ∈ c.support) (hb : b ∈ c.support) (hab : a ≠ b)
    (hp : p.IsPath) (hpint : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support)
    (hpedge : ∀ e ∈ p.edges, e ∉ c.edges) :
    ∃ u w : V, c.length = 4 ∧ Even p.length ∧ 2 ≤ p.length ∧
      G.Adj a u ∧ G.Adj u b ∧ G.Adj a w ∧ G.Adj w b ∧
      u ≠ w ∧ u ≠ a ∧ u ≠ b ∧ w ≠ a ∧ w ≠ b ∧
      s(a, u) ∈ c.edges ∧ s(u, b) ∈ c.edges ∧ s(a, w) ∈ c.edges ∧ s(w, b) ∈ c.edges ∧
      (∀ z, z ∈ c.support → z = a ∨ z = u ∨ z = b ∨ z = w) := by
  obtain ⟨A, B, α, β, hα1, hβ1, hsum, hAarm, hBarm, hABdisj, hAsup, hBsup, hAedge, hBedge,
    hsurj⟩ := exists_arcs_of_cycle hc ha hb hab
  have hParm : IsArm G a b p.getVert p.length := isArm_of_walk p hp hab
  -- an arc and `P₁` are internally disjoint, because `P₁`'s interior misses `C₁`
  have hout : ∀ t', 0 < t' → t' < p.length → p.getVert t' ∉ c.support := by
    intro t' ht0 htl
    exact hpint _ (p.getVert_mem_support t') (hParm.2.2.2.2.1 t' ht0 htl).1
      (hParm.2.2.2.2.1 t' ht0 htl).2
  have hAPdisj : ArmsDisj A α p.getVert p.length := by
    intro t t' ht0 htα ht0' ht'l he
    exact hout t' ht0' ht'l (he ▸ hAsup t (by omega))
  have hBPdisj : ArmsDisj B β p.getVert p.length := by
    intro t t' ht0 htβ ht0' ht'l he
    exact hout t' ht0' ht'l (he ▸ hBsup t (by omega))
  -- at most one of the three arms has length one
  have h3 : 3 ≤ c.length := hc.three_le_length
  have hne1 : ¬ (α = 1 ∧ β = 1) := by rintro ⟨rfl, rfl⟩; omega
  have hpe : ∀ γ : ℕ, ∀ C : ℕ → V, IsArm G a b C γ →
      (∀ t, t < γ → s(C t, C (t + 1)) ∈ c.edges) → ¬ (γ = 1 ∧ p.length = 1) := by
    rintro γ C hC hCe ⟨rfl, hl⟩
    have h1 : s(a, b) ∈ c.edges := by
      have := hCe 0 (by omega)
      rwa [hC.2.1, hC.2.2.1] at this
    have h2 : s(a, b) ∈ p.edges := by
      have := getVert_mem_edges p (i := 0) (by omega)
      rwa [p.getVert_zero, show (0 : ℕ) + 1 = p.length from by omega, p.getVert_length] at this
    exact hpedge _ h2 h1
  have hne2 : ¬ (α = 1 ∧ p.length = 1) := hpe α A hAarm hAedge
  have hne3 : ¬ (β = 1 ∧ p.length = 1) := hpe β B hBarm hBedge
  -- step 4 proper: the shape must be good
  have hgoodd : (α = 2 ∧ β = 2 ∧ Even p.length) ∨ (α = 2 ∧ p.length = 2 ∧ Even β) ∨
      (β = 2 ∧ p.length = 2 ∧ Even α) := by
    by_contra hcon
    exact not_choosable_two_of_three_arms hab hAarm hBarm hParm hABdisj hAPdisj hBPdisj
      hne1 hne2 hne3 hcon hch
  -- the two arcs are the short arms: otherwise the square they make with `P₁` beats `C₁`
  have hsq : ∀ γ δ : ℕ, ∀ C D : ℕ → V, IsArm G a b C γ → IsArm G a b D δ →
      ArmsDisj C γ D δ → γ = 2 → δ = 2 → c.length ≤ 4 := by
    intro γ δ C D hC hD hCD hγ hδ
    subst hγ; subst hδ
    obtain ⟨d, hd, hdl⟩ := exists_isCycle_four
      (x := C 1) (y := D 1)
      (hC.2.1 ▸ hC.2.2.2.1 0 (by omega))
      (hC.2.2.1 ▸ hC.2.2.2.1 1 (by omega))
      ((hD.2.2.1 ▸ hD.2.2.2.1 1 (by omega)).symm)
      ((hD.2.1 ▸ hD.2.2.2.1 0 (by omega)).symm)
      hab (hCD 1 1 (by omega) (by omega) (by omega) (by omega))
    exact hdl ▸ hmin _ d hd
  have hαβ : α = 2 ∧ β = 2 ∧ Even p.length := by
    rcases hgoodd with h | h | h
    · exact h
    · obtain ⟨hα, hl, hev⟩ := h
      have := hsq α p.length A p.getVert hAarm hParm hAPdisj hα hl
      have hβ2 : β = 2 := by
        rcases hev with ⟨r, hr⟩
        omega
      exact ⟨hα, hβ2, ⟨1, by omega⟩⟩
    · obtain ⟨hβ, hl, hev⟩ := h
      have := hsq β p.length B p.getVert hBarm hParm hBPdisj hβ hl
      have hα2 : α = 2 := by
        rcases hev with ⟨r, hr⟩
        omega
      exact ⟨hα2, hβ, ⟨1, by omega⟩⟩
  obtain ⟨hα2, hβ2, hev⟩ := hαβ
  subst hα2; subst hβ2
  have hl2 : 2 ≤ p.length := by
    rcases hev with ⟨r, hr⟩
    have := hParm.1
    omega
  refine ⟨A 1, B 1, by omega, hev, hl2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAarm.2.1 ▸ hAarm.2.2.2.1 0 (by omega)
  · exact hAarm.2.2.1 ▸ hAarm.2.2.2.1 1 (by omega)
  · exact hBarm.2.1 ▸ hBarm.2.2.2.1 0 (by omega)
  · exact hBarm.2.2.1 ▸ hBarm.2.2.2.1 1 (by omega)
  · exact hABdisj 1 1 (by omega) (by omega) (by omega) (by omega)
  · exact (hAarm.2.2.2.2.1 1 (by omega) (by omega)).1
  · exact (hAarm.2.2.2.2.1 1 (by omega) (by omega)).2
  · exact (hBarm.2.2.2.2.1 1 (by omega) (by omega)).1
  · exact (hBarm.2.2.2.2.1 1 (by omega) (by omega)).2
  · have := hAedge 0 (by omega); rwa [hAarm.2.1] at this
  · have := hAedge 1 (by omega); rwa [hAarm.2.2.1] at this
  · have := hBedge 0 (by omega); rwa [hBarm.2.1] at this
  · have := hBedge 1 (by omega); rwa [hBarm.2.2.1] at this
  · intro z hz
    rcases hsurj z hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact Or.inl hAarm.2.1
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl hAarm.2.2.1))
    · have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact Or.inl hBarm.2.1
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl hBarm.2.2.1))


/-! ### Rubin's step 6: the cases on the ends of `P₂`

After step 4 the graph contains `θ_{2,2,L}` — a four-cycle `a, u, b, w` together with a path
`p` of even length `L ≥ 2` from `a` to `b` — and Rubin's step 5 produces a further path `P₂`
joining two of its vertices, internally disjoint from it and edge-disjoint from it. The cases
below are Rubin's (iii)–(vi); his (i) and (ii) are `ListColoring.case_onP1` here, which does not
produce a theta but two cycles meeting in at most one vertex, and so is discharged by his step 3
(see the note on cases (i) and (ii) in `ListColoring.RubinStructure`).

The data of the configuration is passed explicitly rather than bundled, so that the symmetries
`u ↔ w` and `a ↔ b` are available simply by instantiating the same lemma differently. -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A single edge is an arm of length one. -/
theorem isArm_edge {s t : V} (h : G.Adj s t) :
    IsArm G s t (fun j => if j = 0 then s else t) 1 := by
  refine ⟨le_refl 1, by simp, by simp, ?_, ?_, ?_⟩
  · intro j hj
    have : j = 0 := by omega
    subst this
    simpa using h
  · intro j hj0 hj1; omega
  · intro j j' hj0 hj1; omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A path of length two is an arm. -/
theorem isArm_two {s m t : V} (h1 : G.Adj s m) (h2 : G.Adj m t) :
    IsArm G s t (fun j => if j = 0 then s else if j = 1 then m else t) 2 := by
  refine ⟨by omega, by simp, by simp, ?_, ?_, ?_⟩
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simpa using ‹_›
  · intro j hj0 hj2
    have : j = 1 := by omega
    subst this
    exact ⟨by simpa using h1.ne', by simpa using h2.ne⟩
  · intro j j' hj0 hj2 hj0' hj2' _; omega

/-- **Rubin's case (v).** `P₂` joins the two branch vertices `a` and `b`, giving four internally
disjoint arms and so his type `5`. Rubin splits this case further, on whether `|P₁| = 2`; the
sub-split is unnecessary (and, without minimality of `P₁`, wrong — see the note on case (v) in
`ListColoring.RubinStructure`), since four arms are already type `5`. -/
theorem case_branches {a u b w : V} {L M : ℕ} {p q : ℕ → V}
    (hau : G.Adj a u) (hub : G.Adj u b) (haw : G.Adj a w) (hwb : G.Adj w b)
    (hab : a ≠ b) (huw : u ≠ w)
    (hParm : IsArm G a b p L) (hL : 2 ≤ L)
    (hpu : ∀ t, 0 < t → t < L → p t ≠ u) (hpw : ∀ t, 0 < t → t < L → p t ≠ w)
    (hM : 1 ≤ M) (hq0 : q 0 = a) (hqM : q M = b)
    (hqadj : ∀ j, j < M → G.Adj (q j) (q (j + 1)))
    (hqinj : ∀ j j', j ≤ M → j' ≤ M → q j = q j' → j = j')
    (hqint : ∀ j, 0 < j → j < M →
      q j ≠ a ∧ q j ≠ u ∧ q j ≠ b ∧ q j ≠ w ∧ ∀ t, t ≤ L → q j ≠ p t) :
    ¬ G.Choosable 2 := by
  have hQarm : IsArm G a b q M := by
    refine ⟨hM, hq0, hqM, hqadj, ?_, ?_⟩
    · intro j hj0 hjM
      exact ⟨(hqint j hj0 hjM).1, (hqint j hj0 hjM).2.2.1⟩
    · intro j j' hj0 hjM hj0' hj'M he
      exact hqinj j j' (by omega) (by omega) he
  refine not_choosable_two_of_four_arms (P := q) (Q := fun j => if j = 0 then a else
      if j = 1 then u else b) (R := fun j => if j = 0 then a else if j = 1 then w else b)
    (S := p) hab (by omega) (by omega) hL hQarm (isArm_two hau hub) (isArm_two haw hwb) hParm
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro j j' hj0 hjM hj0' hj'2 he
    have : j' = 1 := by omega
    subst this
    exact (hqint j hj0 hjM).2.1 (by simpa using he)
  · intro j j' hj0 hjM hj0' hj'2 he
    have : j' = 1 := by omega
    subst this
    exact (hqint j hj0 hjM).2.2.2.1 (by simpa using he)
  · intro j j' hj0 hjM hj0' hj'L he
    exact (hqint j hj0 hjM).2.2.2.2 j' (by omega) he
  · intro j j' hj0 hj2 hj0' hj'2 he
    have e1 : j = 1 := by omega
    have e2 : j' = 1 := by omega
    subst e1; subst e2
    exact huw (by simpa using he)
  · intro j j' hj0 hj2 hj0' hj'L he
    have : j = 1 := by omega
    subst this
    have he' : u = p j' := by simpa using he
    exact hpu j' hj0' hj'L he'.symm
  · intro j j' hj0 hj2 hj0' hj'L he
    have : j = 1 := by omega
    subst this
    have he' : w = p j' := by simpa using he
    exact hpw j' hj0' hj'L he'.symm

/-- **Rubin's case (vi).** `P₂` joins the two arc middles `u` and `w`. Rubin says "delete any
edge of `C₁` to expose a `θ`"; concretely the branch vertices are `u` and `b`, with arms the edge
`u — b`, the path `u — a` followed by `P₁`, and `P₂` followed by the edge `w — b`. Type `4`. -/
theorem case_middles {a u b w : V} {L M : ℕ} {p q : ℕ → V}
    (hau : G.Adj a u) (hub : G.Adj u b) (haw : G.Adj a w) (hwb : G.Adj w b)
    (hab : a ≠ b) (huw : u ≠ w)
    (hParm : IsArm G a b p L) (hL : 2 ≤ L)
    (hpu : ∀ t, 0 < t → t < L → p t ≠ u) (hpw : ∀ t, 0 < t → t < L → p t ≠ w)
    (hM : 1 ≤ M) (hq0 : q 0 = u) (hqM : q M = w)
    (hqadj : ∀ j, j < M → G.Adj (q j) (q (j + 1)))
    (hqinj : ∀ j j', j ≤ M → j' ≤ M → q j = q j' → j = j')
    (hqint : ∀ j, 0 < j → j < M →
      q j ≠ a ∧ q j ≠ u ∧ q j ≠ b ∧ q j ≠ w ∧ ∀ t, t ≤ L → q j ≠ p t) :
    ¬ G.Choosable 2 := by
  have hp0 : p 0 = a := hParm.2.1
  have hpL : p L = b := hParm.2.2.1
  have hpne : ∀ t, 0 < t → t < L → p t ≠ a ∧ p t ≠ b := hParm.2.2.2.2.1
  have hpinj : ∀ t t', 0 < t → t < L → 0 < t' → t' < L → p t = p t' → t = t' :=
    hParm.2.2.2.2.2
  -- the second arm: the edge `u — a` followed by `P₁`
  have harm2 : IsArm G u b (fun j => if j = 0 then u else p (j - 1)) (L + 1) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · show (if (0 : ℕ) = 0 then u else p (0 - 1)) = u
      rw [if_pos rfl]
    · show (if L + 1 = 0 then u else p (L + 1 - 1)) = b
      rw [if_neg (by omega), show L + 1 - 1 = L from by omega]
      exact hpL
    · intro j hj
      show G.Adj (if j = 0 then u else p (j - 1)) (if j + 1 = 0 then u else p (j + 1 - 1))
      rw [if_neg (by omega : ¬ (j + 1 = 0)), show j + 1 - 1 = j from by omega]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [if_pos rfl, hp0]; exact hau.symm
      · rw [if_neg (by omega : ¬ (j = 0)), show j = (j - 1) + 1 from by omega]
        exact hParm.2.2.2.1 (j - 1) (by omega)
    · intro j hj0 hjL
      show (if j = 0 then u else p (j - 1)) ≠ u ∧ (if j = 0 then u else p (j - 1)) ≠ b
      rw [if_neg (by omega : ¬ (j = 0))]
      rcases Nat.eq_zero_or_pos (j - 1) with h | h
      · rw [h, hp0]; exact ⟨hau.ne, hab⟩
      · exact ⟨hpu (j - 1) h (by omega), (hpne (j - 1) h (by omega)).2⟩
    · intro j j' hj0 hjL hj0' hj'L he
      have he' : p (j - 1) = p (j' - 1) := by
        simpa only [if_neg (by omega : ¬ (j = 0)), if_neg (by omega : ¬ (j' = 0))] using he
      rcases Nat.eq_zero_or_pos (j - 1) with h | h
      · rcases Nat.eq_zero_or_pos (j' - 1) with h' | h'
        · omega
        · rw [h, hp0] at he'
          exact absurd he'.symm (hpne (j' - 1) h' (by omega)).1
      · rcases Nat.eq_zero_or_pos (j' - 1) with h' | h'
        · rw [h', hp0] at he'
          exact absurd he' (hpne (j - 1) h (by omega)).1
        · have := hpinj (j - 1) (j' - 1) h (by omega) h' (by omega) he'
          omega
  -- the third arm: `P₂` followed by the edge `w — b`
  have harm3 : IsArm G u b (fun j => if j ≤ M then q j else b) (M + 1) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · show (if (0 : ℕ) ≤ M then q 0 else b) = u
      rw [if_pos (Nat.zero_le M)]; exact hq0
    · show (if M + 1 ≤ M then q (M + 1) else b) = b
      rw [if_neg (by omega)]
    · intro j hj
      show G.Adj (if j ≤ M then q j else b) (if j + 1 ≤ M then q (j + 1) else b)
      rcases Nat.lt_or_ge j M with h | h
      · rw [if_pos (by omega : j ≤ M), if_pos (by omega : j + 1 ≤ M)]
        exact hqadj j h
      · have hjM : j = M := by omega
        rw [if_pos (by omega : j ≤ M), if_neg (by omega : ¬ (j + 1 ≤ M)), hjM, hqM]
        exact hwb
    · intro j hj0 hjM
      show (if j ≤ M then q j else b) ≠ u ∧ (if j ≤ M then q j else b) ≠ b
      rw [if_pos (by omega : j ≤ M)]
      rcases Nat.lt_or_ge j M with h | h
      · exact ⟨(hqint j hj0 h).2.1, (hqint j hj0 h).2.2.1⟩
      · have hjM' : j = M := by omega
        rw [hjM', hqM]
        exact ⟨fun he => huw he.symm, hwb.ne⟩
    · intro j j' hj0 hjM hj0' hj'M he
      have he' : q j = q j' := by
        simpa only [if_pos (by omega : j ≤ M), if_pos (by omega : j' ≤ M)] using he
      exact hqinj j j' (by omega) (by omega) he'
  refine not_choosable_two_of_arm_one (P := fun j => if j = 0 then u else b)
    (Q := fun j => if j = 0 then u else p (j - 1)) (R := fun j => if j ≤ M then q j else b)
    hub.ne (by omega) (by omega) (isArm_edge hub) harm2 harm3 ?_ ?_ ?_
  · intro j j' hj0 hj1; omega
  · intro j j' hj0 hj1; omega
  · intro j j' hj0 hjL hj0' hj'M he
    have he' : p (j - 1) = q j' := by
      simpa only [if_neg (by omega : ¬ (j = 0)), if_pos (by omega : j' ≤ M)] using he
    rcases Nat.lt_or_ge j' M with h | h
    · exact (hqint j' hj0' h).2.2.2.2 (j - 1) (by omega) he'.symm
    · have hj'M' : j' = M := by omega
      rw [hj'M', hqM] at he'
      rcases Nat.eq_zero_or_pos (j - 1) with h0 | h0
      · rw [h0, hp0] at he'
        exact haw.ne he'
      · exact hpw (j - 1) h0 (by omega) he'


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A path of length three is an arm. -/
theorem isArm_three {s m₁ m₂ t : V} (h1 : G.Adj s m₁) (h2 : G.Adj m₁ m₂) (h3 : G.Adj m₂ t)
    (h1t : m₁ ≠ t) (h2s : m₂ ≠ s) (h12 : m₁ ≠ m₂) :
    IsArm G s t
      (fun j => if j = 0 then s else if j = 1 then m₁ else if j = 2 then m₂ else t) 3 := by
  refine ⟨by omega, by simp, by simp, ?_, ?_, ?_⟩
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simpa using ‹_›
  · intro j hj0 hj3
    have : j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl
    · exact ⟨by simpa using h1.ne', by simpa using h1t⟩
    · exact ⟨by simpa using h2s, by simpa using h3.ne⟩
  · intro j j' hj0 hj3 hj0' hj'3 he
    have e1 : j = 1 ∨ j = 2 := by omega
    have e2 : j' = 1 ∨ j' = 2 := by omega
    rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl
    · rfl
    · exact absurd (by simpa using he) h12
    · exact absurd (show m₂ = m₁ by simpa using he).symm h12
    · rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An arm repeats no vertex at all, its two ends included. -/
theorem IsArm.inj_all {s t : V} {P : ℕ → V} {k : ℕ} (h : IsArm G s t P k) (hst : s ≠ t)
    (j j' : ℕ) (hj : j ≤ k) (hj' : j' ≤ k) (he : P j = P j') : j = j' := by
  obtain ⟨hk, h0, hk', -, hint, hinj⟩ := h
  have key : ∀ i, i ≤ k → (i = 0 ∧ P i = s) ∨ (i = k ∧ P i = t) ∨ (0 < i ∧ i < k) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · exact Or.inl ⟨hi0, by rw [hi0]; exact h0⟩
    · rcases Nat.lt_or_ge i k with hlt | hge
      · exact Or.inr (Or.inr ⟨hi0, hlt⟩)
      · exact Or.inr (Or.inl ⟨by omega, by rw [show i = k from by omega]; exact hk'⟩)
  rcases key j hj with ⟨e1, v1⟩ | ⟨e1, v1⟩ | ⟨e1, e1'⟩ <;>
    rcases key j' hj' with ⟨e2, v2⟩ | ⟨e2, v2⟩ | ⟨e2, e2'⟩
  · omega
  · exact absurd (show s = t by rw [← v1, ← v2]; exact he) hst
  · exact absurd (show s = P j' by rw [← v1]; exact he).symm (hint j' e2 e2').1
  · exact absurd (show t = s by rw [← v1, ← v2]; exact he).symm hst
  · omega
  · exact absurd (show t = P j' by rw [← v1]; exact he).symm (hint j' e2 e2').2
  · exact absurd (show P j = s by rw [he]; exact v2) (hint j e1 e1').1
  · exact absurd (show P j = t by rw [he]; exact v2) (hint j e1 e1').2
  · exact hinj j j' e1 e1' e2 e2' he

/-- **Rubin's case (iv).** `P₂` joins a branch vertex `a` to an arc middle `u`. The branch
vertices of the exposed theta are `u` and `a` itself, with arms the edge `u — a`, the path
`u — b — w — a` and `P₂`. Type `4`. -/
theorem case_mixed {a u b w : V} {M : ℕ} {q : ℕ → V}
    (hau : G.Adj a u) (hub : G.Adj u b) (haw : G.Adj a w) (hwb : G.Adj w b)
    (hab : a ≠ b) (huw : u ≠ w)
    (hM : 2 ≤ M) (hq0 : q 0 = u) (hqM : q M = a)
    (hqadj : ∀ j, j < M → G.Adj (q j) (q (j + 1)))
    (hqinj : ∀ j j', j ≤ M → j' ≤ M → q j = q j' → j = j')
    (hqint : ∀ j, 0 < j → j < M → q j ≠ a ∧ q j ≠ u ∧ q j ≠ b ∧ q j ≠ w) :
    ¬ G.Choosable 2 := by
  have hQarm : IsArm G u a q M := by
    refine ⟨by omega, hq0, hqM, hqadj, ?_, ?_⟩
    · exact fun j hj0 hjM => ⟨(hqint j hj0 hjM).2.1, (hqint j hj0 hjM).1⟩
    · exact fun j j' hj0 hjM hj0' hj'M he => hqinj j j' (by omega) (by omega) he
  refine not_choosable_two_of_arm_one (P := fun j => if j = 0 then u else a)
    (Q := fun j => if j = 0 then u else if j = 1 then b else if j = 2 then w else a) (R := q)
    hau.ne' (by omega) hM (isArm_edge hau.symm)
    (isArm_three hub hwb.symm haw.symm hab.symm huw.symm hwb.ne') hQarm ?_ ?_ ?_
  · intro j j' hj0 hj1; omega
  · intro j j' hj0 hj1; omega
  · intro j j' hj0 hj3 hj0' hj'M he
    have e1 : j = 1 ∨ j = 2 := by omega
    rcases e1 with rfl | rfl
    · exact (hqint j' hj0' hj'M).2.2.1 (show b = q j' by simpa using he).symm
    · exact (hqint j' hj0' hj'M).2.2.2 (show w = q j' by simpa using he).symm

/-- **Rubin's case (iii).** `P₂` joins an arc middle `u` to an interior vertex `p k` of `P₁`.
The branch vertices of the exposed theta are `u` and `a`, with arms the edge `u — a`, the path
`u — b — w — a`, and `P₂` followed by `P₁` traversed backwards from `p k` to `a`. Type `4`. -/
theorem case_interior {a u b w : V} {L M k : ℕ} {p q : ℕ → V}
    (hau : G.Adj a u) (hub : G.Adj u b) (haw : G.Adj a w) (hwb : G.Adj w b)
    (hab : a ≠ b) (huw : u ≠ w)
    (hParm : IsArm G a b p L) (hL : 2 ≤ L)
    (hpu : ∀ t, 0 < t → t < L → p t ≠ u) (hpw : ∀ t, 0 < t → t < L → p t ≠ w)
    (hk0 : 0 < k) (hkL : k < L)
    (hM : 1 ≤ M) (hq0 : q 0 = u) (hqM : q M = p k)
    (hqadj : ∀ j, j < M → G.Adj (q j) (q (j + 1)))
    (hqinj : ∀ j j', j ≤ M → j' ≤ M → q j = q j' → j = j')
    (hqint : ∀ j, 0 < j → j < M →
      q j ≠ a ∧ q j ≠ u ∧ q j ≠ b ∧ q j ≠ w ∧ ∀ t, t ≤ L → q j ≠ p t) :
    ¬ G.Choosable 2 := by
  have hp0 : p 0 = a := hParm.2.1
  have hpne : ∀ t, 0 < t → t < L → p t ≠ a ∧ p t ≠ b := hParm.2.2.2.2.1
  have hpinj := hParm.inj_all hab
  -- the third arm: `P₂` followed by `P₁` backwards
  set R : ℕ → V := fun j => if j ≤ M then q j else p (k - (j - M)) with hR
  have hRM : ∀ j, M ≤ j → j ≤ M + k → R j = p (k - (j - M)) := by
    intro j hj1 hj2
    rcases Nat.eq_or_lt_of_le hj1 with h | h
    · have hjM : j = M := h.symm
      subst hjM
      simp only [hR]
      rw [if_pos (le_refl j), Nat.sub_self, Nat.sub_zero]
      exact hqM
    · simp only [hR, if_neg (by omega : ¬ (j ≤ M))]
  have harm3 : IsArm G u a R (M + k) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hR, if_pos (Nat.zero_le M)]; exact hq0
    · rw [hRM (M + k) (by omega) (by omega), show k - (M + k - M) = 0 from by omega]; exact hp0
    · intro j hj
      rcases Nat.lt_or_ge j M with h | h
      · simp only [hR, if_pos (by omega : j ≤ M), if_pos (by omega : j + 1 ≤ M)]
        exact hqadj j h
      · rw [hRM j (by omega) (by omega), hRM (j + 1) (by omega) (by omega)]
        have := hParm.2.2.2.1 (k - (j + 1 - M)) (by omega)
        rw [show k - (j + 1 - M) + 1 = k - (j - M) from by omega] at this
        exact this.symm
    · intro j hj0 hjMk
      rcases Nat.lt_or_ge j M with h | h
      · simp only [hR, if_pos (by omega : j ≤ M)]
        exact ⟨(hqint j hj0 h).2.1, (hqint j hj0 h).1⟩
      · rw [hRM j (by omega) (by omega)]
        exact ⟨hpu (k - (j - M)) (by omega) (by omega),
          (hpne (k - (j - M)) (by omega) (by omega)).1⟩
    · intro j j' hj0 hjMk hj0' hj'Mk he
      rcases Nat.lt_or_ge j M with h | h <;> rcases Nat.lt_or_ge j' M with h' | h'
      · have he' : q j = q j' := by
          simpa only [hR, if_pos (by omega : j ≤ M), if_pos (by omega : j' ≤ M)] using he
        exact hqinj j j' (by omega) (by omega) he'
      · rw [hRM j' (by omega) (by omega)] at he
        simp only [hR, if_pos (by omega : j ≤ M)] at he
        exact absurd he ((hqint j hj0 h).2.2.2.2 (k - (j' - M)) (by omega))
      · rw [hRM j (by omega) (by omega)] at he
        simp only [hR, if_pos (by omega : j' ≤ M)] at he
        exact absurd he.symm ((hqint j' hj0' h').2.2.2.2 (k - (j - M)) (by omega))
      · rw [hRM j (by omega) (by omega), hRM j' (by omega) (by omega)] at he
        have := hpinj (k - (j - M)) (k - (j' - M)) (by omega) (by omega) he
        omega
  refine not_choosable_two_of_arm_one (P := fun j => if j = 0 then u else a)
    (Q := fun j => if j = 0 then u else if j = 1 then b else if j = 2 then w else a) (R := R)
    hau.ne' (by omega) (by omega) (isArm_edge hau.symm)
    (isArm_three hub hwb.symm haw.symm hab.symm huw.symm hwb.ne') harm3 ?_ ?_ ?_
  · intro j j' hj0 hj1; omega
  · intro j j' hj0 hj1; omega
  · intro j j' hj0 hj3 hj0' hj'Mk he
    have hval : R j' = b ∨ R j' = w → False := by
      rintro (hb | hw)
      · rcases Nat.lt_or_ge j' M with h | h
        · exact (hqint j' hj0' h).2.2.1 (by simpa only [hR, if_pos (by omega : j' ≤ M)] using hb)
        · rw [hRM j' (by omega) (by omega)] at hb
          exact (hpne (k - (j' - M)) (by omega) (by omega)).2 hb
      · rcases Nat.lt_or_ge j' M with h | h
        · exact (hqint j' hj0' h).2.2.2.1 (by simpa only [hR, if_pos (by omega : j' ≤ M)] using hw)
        · rw [hRM j' (by omega) (by omega)] at hw
          exact hpw (k - (j' - M)) (by omega) (by omega) hw
    have e1 : j = 1 ∨ j = 2 := by omega
    rcases e1 with rfl | rfl
    · exact hval (Or.inl (by simpa using he.symm))
    · exact hval (Or.inr (by simpa using he.symm))


set_option maxHeartbeats 800000 in
/-- **Rubin's cases (i) and (ii), merged.** `P₂` joins two vertices `p α` and `p β` of `P₁` that
are not its two ends. The cycle `p α, …, p β` closed by `P₂` then meets the four-cycle
`a, u, b, w` in at most the single vertex `p α`, so the graph carries two cycles joined by a path
and otherwise disjoint — Rubin's types `2` and `3`, which
`ListColoring.not_choosable_two_of_dumbbell` covers together.

Rubin treats these as two cases and remarks that they return him to his earlier ones; his step 3
has in fact already excluded them, so they cannot occur at all (see the note on cases (i) and (ii)
in `ListColoring.RubinStructure`). They are nevertheless discharged here directly, which is
cheaper than re-deriving the step-3 hypothesis. -/
theorem case_onP1 {a u b w : V} {L M α β : ℕ} {p q : ℕ → V}
    (hau : G.Adj a u) (hub : G.Adj u b) (haw : G.Adj a w) (hwb : G.Adj w b)
    (hab : a ≠ b) (huw : u ≠ w)
    (hParm : IsArm G a b p L) (hL : 2 ≤ L)
    (hpu : ∀ t, 0 < t → t < L → p t ≠ u) (hpw : ∀ t, 0 < t → t < L → p t ≠ w)
    (hαβ : α < β) (hβL : β < L)
    (hM : 1 ≤ M) (hq0 : q 0 = p α) (hqM : q M = p β)
    (hqadj : ∀ j, j < M → G.Adj (q j) (q (j + 1)))
    (hqinj : ∀ j j', j ≤ M → j' ≤ M → q j = q j' → j = j')
    (hqint : ∀ j, 0 < j → j < M →
      q j ≠ a ∧ q j ≠ u ∧ q j ≠ b ∧ q j ≠ w ∧ ∀ t, t ≤ L → q j ≠ p t)
    (hdm : 3 ≤ (β - α) + M) :
    ¬ G.Choosable 2 := by
  have hp0 : p 0 = a := hParm.2.1
  have hpne : ∀ t, 0 < t → t < L → p t ≠ a ∧ p t ≠ b := hParm.2.2.2.2.1
  have hpadj : ∀ t, t < L → G.Adj (p t) (p (t + 1)) := hParm.2.2.2.1
  have hpinj := hParm.inj_all hab
  have dau : a ≠ u := hau.ne
  have daw : a ≠ w := haw.ne
  have dub : u ≠ b := hub.ne
  have dbw : b ≠ w := hwb.ne'
  set A : ℕ → V := fun i => if i = 0 then a else if i = 1 then u else if i = 2 then b else w
    with hAdef
  have hA0 : A 0 = a := by simp [hAdef]
  have hA1 : A 1 = u := by simp [hAdef]
  have hA2 : A 2 = b := by simp [hAdef]
  have hA3 : A 3 = w := by simp [hAdef]
  set B : ℕ → V := fun t => if t ≤ β - α then p (α + t) else q (M - (t - (β - α))) with hBdef
  have hB1 : ∀ t, t ≤ β - α → B t = p (α + t) := by
    intro t ht; simp only [hBdef, if_pos ht]
  have hB2 : ∀ t, β - α < t → B t = q (M - (t - (β - α))) := by
    intro t ht; simp only [hBdef, if_neg (by omega : ¬ (t ≤ β - α))]
  -- the far end of `P₂`, read from the `p` side
  have hqadj0 : G.Adj (p α) (q 1) := by rw [← hq0]; exact hqadj 0 (by omega)
  have hBn : B ((β - α) + M - 1) = q 1 := by
    rcases (by omega : M = 1 ∨ 2 ≤ M) with hM1 | hM2
    · rw [hB1 _ (by omega), show α + ((β - α) + M - 1) = β from by omega, ← hqM,
        show M = 1 from hM1]
    · rw [hB2 _ (by omega), show M - ((β - α) + M - 1 - (β - α)) = 1 from by omega]
  refine not_choosable_two_of_dumbbell (m := 3) (n := (β - α) + M - 1) (l := α)
    (by omega) (by omega) A p B ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hA0, hA1]; exact hau
    · rw [hA1, hA2]; exact hub
    · rw [hA2, hA3]; exact hwb.symm
  · rw [hA3, hA0]; exact haw.symm
  · exact fun j hj => hpadj j (by omega)
  · intro t ht
    rcases (by omega : t + 1 ≤ β - α ∨ t = β - α ∨ β - α < t) with h | h | h
    · rw [hB1 t (by omega), hB1 (t + 1) (by omega),
        show α + (t + 1) = (α + t) + 1 from by omega]
      exact hpadj (α + t) (by omega)
    · rw [hB1 t (by omega), hB2 (t + 1) (by omega),
        show M - (t + 1 - (β - α)) = M - 1 from by omega, show α + t = β from by omega, ← hqM]
      have := hqadj (M - 1) (by omega)
      rw [show M - 1 + 1 = M from by omega] at this
      exact this.symm
    · rw [hB2 t (by omega), hB2 (t + 1) (by omega)]
      have := hqadj (M - (t + 1 - (β - α))) (by omega)
      rw [show M - (t + 1 - (β - α)) + 1 = M - (t - (β - α)) from by omega] at this
      exact this.symm
  · rw [hBn, hB1 0 (by omega), Nat.add_zero]
    exact hqadj0.symm
  · rw [hA0]; exact hp0
  · rw [hB1 0 (by omega), Nat.add_zero]
  · intro i hi i' hi' he
    simp only [Set.mem_Iic] at hi hi'
    have hAval : ∀ n, n ≤ 3 → (A n = a ∧ n = 0) ∨ (A n = u ∧ n = 1) ∨ (A n = b ∧ n = 2) ∨
        (A n = w ∧ n = 3) := by
      intro n hn
      have hn4 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hn4 with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨hA0, rfl⟩
      · exact Or.inr (Or.inl ⟨hA1, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hA2, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hA3, rfl⟩))
    rcases hAval i hi with ⟨v1, e1⟩ | ⟨v1, e1⟩ | ⟨v1, e1⟩ | ⟨v1, e1⟩ <;>
      rcases hAval i' hi' with ⟨v2, e2⟩ | ⟨v2, e2⟩ | ⟨v2, e2⟩ | ⟨v2, e2⟩ <;>
      rw [v1, v2] at he <;>
      first
        | omega
        | exact absurd he (by assumption)
        | exact absurd he.symm (by assumption)
  · intro j hj j' hj'
    simp only [Set.mem_Iic] at hj hj'
    exact fun he => hpinj j j' (by omega) (by omega) he
  · intro t ht t' ht' he
    simp only [Set.mem_Iic] at ht ht'
    rcases (by omega : t ≤ β - α ∨ β - α < t) with h | h <;>
      rcases (by omega : t' ≤ β - α ∨ β - α < t') with h' | h'
    · rw [hB1 t h, hB1 t' h'] at he
      have := hpinj (α + t) (α + t') (by omega) (by omega) he
      omega
    · rw [hB1 t h, hB2 t' h'] at he
      exact absurd he.symm
        ((hqint _ (by omega) (by omega)).2.2.2.2 (α + t) (by omega))
    · rw [hB2 t h, hB1 t' h'] at he
      exact absurd he ((hqint _ (by omega) (by omega)).2.2.2.2 (α + t') (by omega))
    · rw [hB2 t h, hB2 t' h'] at he
      have := hqinj _ _ (by omega) (by omega) he
      omega
  · intro i hi j hj1 hj2
    have hjint : p j ≠ a ∧ p j ≠ b := hpne j (by omega) (by omega)
    have e1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases e1 with rfl | rfl | rfl | rfl
    · rw [hA0]; exact fun he => hjint.1 he.symm
    · rw [hA1]; exact fun he => hpu j (by omega) (by omega) he.symm
    · rw [hA2]; exact fun he => hjint.2 he.symm
    · rw [hA3]; exact fun he => hpw j (by omega) (by omega) he.symm
  · intro i hi k hk1 hk2
    have e1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases (by omega : k ≤ β - α ∨ β - α < k) with h | h
    · rw [hB1 k h]
      have hjint : p (α + k) ≠ a ∧ p (α + k) ≠ b := hpne (α + k) (by omega) (by omega)
      rcases e1 with rfl | rfl | rfl | rfl
      · rw [hA0]; exact fun he => hjint.1 he.symm
      · rw [hA1]; exact fun he => hpu (α + k) (by omega) (by omega) he.symm
      · rw [hA2]; exact fun he => hjint.2 he.symm
      · rw [hA3]; exact fun he => hpw (α + k) (by omega) (by omega) he.symm
    · rw [hB2 k h]
      have hqi := hqint (M - (k - (β - α))) (by omega) (by omega)
      rcases e1 with rfl | rfl | rfl | rfl
      · rw [hA0]; exact fun he => hqi.1 he.symm
      · rw [hA1]; exact fun he => hqi.2.1 he.symm
      · rw [hA2]; exact fun he => hqi.2.2.1 he.symm
      · rw [hA3]; exact fun he => hqi.2.2.2.1 he.symm
  · intro j hj k hk1 hk2
    rcases (by omega : k ≤ β - α ∨ β - α < k) with h | h
    · rw [hB1 k h]
      intro he
      have := hpinj j (α + k) (by omega) (by omega) he
      omega
    · rw [hB2 k h]
      exact fun he =>
        (hqint (M - (k - (β - α))) (by omega) (by omega)).2.2.2.2 j (by omega) he.symm


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An arm traversed backwards is an arm. -/
theorem IsArm.rev {s t : V} {P : ℕ → V} {k : ℕ} (h : IsArm G s t P k) :
    IsArm G t s (fun j => P (k - j)) k := by
  obtain ⟨hk, h0, hk', hadj, hint, hinj⟩ := h
  refine ⟨hk, ?_, ?_, ?_, ?_, ?_⟩
  · show P (k - 0) = t
    rw [Nat.sub_zero]; exact hk'
  · show P (k - k) = s
    rw [Nat.sub_self]; exact h0
  · intro j hj
    show G.Adj (P (k - j)) (P (k - (j + 1)))
    have := hadj (k - (j + 1)) (by omega)
    rw [show k - (j + 1) + 1 = k - j from by omega] at this
    exact this.symm
  · intro j hj0 hjk
    show P (k - j) ≠ t ∧ P (k - j) ≠ s
    exact ⟨(hint (k - j) (by omega) (by omega)).2, (hint (k - j) (by omega) (by omega)).1⟩
  · intro j j' hj0 hjk hj0' hj'k he
    have he' : P (k - j) = P (k - j') := he
    have := hinj (k - j) (k - j') (by omega) (by omega) (by omega) (by omega) he'
    omega

set_option maxHeartbeats 1000000 in
/-- **Rubin's steps 5 and 6.** With `C₁ ∪ P₁` equal to `θ_{2,2,2m}` — a four-cycle `a, u, b, w`
and a path `P₁` from `a` to `b` of even length — a further edge of `G` outside it is impossible.
Rubin's six cases on the ends of the second connecting path `P₂` are `ListColoring.case_onP1`
(his (i) and (ii)), `ListColoring.case_interior` (iii), `ListColoring.case_mixed` (iv),
`ListColoring.case_branches` (v) and `ListColoring.case_middles` (vi).

Due to A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Congr.
Numer. **26** (1980), 125–157, pp. 132–133. -/
theorem step56 (hconn : G.Connected) (hdeg : ∀ z : V, 2 ≤ G.degree z) (hch : G.Choosable 2)
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) {a b : V} {p : G.Walk a b}
    (hab : a ≠ b) (hp : p.IsPath)
    (hpint : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support)
    {u w : V} (hl2 : 2 ≤ p.length)
    (hau : G.Adj a u) (hub : G.Adj u b) (haw : G.Adj a w) (hwb : G.Adj w b)
    (huw : u ≠ w)
    (heau : s(a, u) ∈ c.edges) (heub : s(u, b) ∈ c.edges) (heaw : s(a, w) ∈ c.edges)
    (hewb : s(w, b) ∈ c.edges)
    (hcsup : ∀ z, z ∈ c.support → z = a ∨ z = u ∨ z = b ∨ z = w)
    (hmore : ∃ x y : V, G.Adj x y ∧ ¬ (s(x, y) ∈ c.edges ∨ s(x, y) ∈ p.edges)) :
    False := by
  classical
  set L : ℕ := p.length with hLdef
  have hParm : IsArm G a b p.getVert L := isArm_of_walk p hp hab
  -- the four vertices of `C₁` lie on `C₁`
  have huc : u ∈ c.support := c.snd_mem_support_of_mem_edges heau
  have hwc : w ∈ c.support := c.snd_mem_support_of_mem_edges heaw
  have hpout : ∀ t, 0 < t → t < L → p.getVert t ∉ c.support := by
    intro t ht0 htL
    exact hpint _ (p.getVert_mem_support t) (hParm.2.2.2.2.1 t ht0 htL).1
      (hParm.2.2.2.2.1 t ht0 htL).2
  have hpu : ∀ t, 0 < t → t < L → p.getVert t ≠ u := fun t h1 h2 he => hpout t h1 h2 (he ▸ huc)
  have hpw : ∀ t, 0 < t → t < L → p.getVert t ≠ w := fun t h1 h2 he => hpout t h1 h2 (he ▸ hwc)
  -- Rubin's `P₂`
  obtain ⟨x₂, y₂, r, hx₂S, hy₂S, hx₂y₂, hr, hr1, hrint, hredge⟩ :=
    exists_connecting_path_of_choosable (S := {z : V | z ∈ c.support ∨ z ∈ p.support})
      (F := {e : Sym2 V | e ∈ c.edges ∨ e ∈ p.edges}) hconn hdeg hch hc
      (fun x hx => Or.inl hx)
      (fun {x y} h => by
        rcases h with h | h
        · exact Or.inl (c.fst_mem_support_of_mem_edges h)
        · exact Or.inr (p.fst_mem_support_of_mem_edges h))
      (by obtain ⟨x, y, hxy, hnot⟩ := hmore; exact ⟨x, y, hxy, hnot⟩)
  set M : ℕ := r.length with hMdef
  have hM1 : 1 ≤ M := hr1
  have hrinj : ∀ j j', j ≤ M → j' ≤ M → r.getVert j = r.getVert j' → j = j' :=
    fun j j' hj hj' he => hr.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he
  have hrout : ∀ j, 0 < j → j < M → r.getVert j ∉ c.support ∧ r.getVert j ∉ p.support := by
    intro j hj0 hjM
    have h1 : r.getVert j ≠ x₂ := by
      intro he
      exact absurd (hrinj j 0 (by omega) (by omega) (by rw [he, r.getVert_zero])) (by omega)
    have h2 : r.getVert j ≠ y₂ := by
      intro he
      exact absurd (hrinj j M (by omega) (by omega) (by rw [he, r.getVert_length])) (by omega)
    have := hrint _ (r.getVert_mem_support j) h1 h2
    simp only [Set.mem_setOf_eq, not_or] at this
    exact this
  -- the interior data both orientations of `P₂` need
  have hdata : ∀ (R : ℕ → V), (∀ j, 0 < j → j < M → ∃ i, 0 < i ∧ i < M ∧ R j = r.getVert i) →
      ∀ j, 0 < j → j < M → R j ≠ a ∧ R j ≠ u ∧ R j ≠ b ∧ R j ≠ w ∧
        ∀ t, t ≤ L → R j ≠ p.getVert t := by
    intro R hR j hj0 hjM
    obtain ⟨i, hi0, hiM, hRi⟩ := hR j hj0 hjM
    obtain ⟨hc1, hc2⟩ := hrout i hi0 hiM
    rw [hRi]
    have hac : a ∈ c.support := c.fst_mem_support_of_mem_edges heau
    have hbc : b ∈ c.support := c.snd_mem_support_of_mem_edges heub
    exact ⟨fun he => hc1 (by rw [he]; exact hac), fun he => hc1 (by rw [he]; exact huc),
      fun he => hc1 (by rw [he]; exact hbc), fun he => hc1 (by rw [he]; exact hwc),
      fun t _ he => hc2 (by rw [he]; exact p.getVert_mem_support t)⟩
  have hfwd : ∀ j, 0 < j → j < M → ∃ i, 0 < i ∧ i < M ∧ r.getVert j = r.getVert i :=
    fun j h1 h2 => ⟨j, h1, h2, rfl⟩
  have hbwd : ∀ j, 0 < j → j < M →
      ∃ i, 0 < i ∧ i < M ∧ (fun k => r.getVert (M - k)) j = r.getVert i :=
    fun j h1 h2 => ⟨M - j, by omega, by omega, rfl⟩
  have hqf := hdata r.getVert hfwd
  have hqr := hdata (fun k => r.getVert (M - k)) hbwd
  have hqfadj : ∀ j, j < M → G.Adj (r.getVert j) (r.getVert (j + 1)) :=
    fun j hj => r.adj_getVert_succ hj
  have hqradj : ∀ j, j < M →
      G.Adj ((fun k => r.getVert (M - k)) j) ((fun k => r.getVert (M - k)) (j + 1)) := by
    intro j hj
    show G.Adj (r.getVert (M - j)) (r.getVert (M - (j + 1)))
    have := r.adj_getVert_succ (i := M - (j + 1)) (by omega)
    rw [show M - (j + 1) + 1 = M - j from by omega] at this
    exact this.symm
  have hqrinj : ∀ j j', j ≤ M → j' ≤ M →
      (fun k => r.getVert (M - k)) j = (fun k => r.getVert (M - k)) j' → j = j' := by
    intro j j' hj hj' he
    have := hrinj (M - j) (M - j') (by omega) (by omega) he
    omega
  have hqf0 : r.getVert 0 = x₂ := r.getVert_zero
  have hqfM : r.getVert M = y₂ := r.getVert_length
  have hqr0 : (fun k => r.getVert (M - k)) 0 = y₂ := by
    show r.getVert (M - 0) = y₂; rw [Nat.sub_zero]; exact hqfM
  have hqrM : (fun k => r.getVert (M - k)) M = x₂ := by
    show r.getVert (M - M) = x₂; rw [Nat.sub_self]; exact hqf0
  -- the single edge of a length-one `P₂` is outside `C₁ ∪ P₁`
  have hredge1 : ¬ (s(r.getVert 0, r.getVert 1) ∈ c.edges ∨
      s(r.getVert 0, r.getVert 1) ∈ p.edges) :=
    hredge _ (getVert_mem_edges r (by omega))
  have hqfe : M = 1 → ¬ (s(r.getVert 0, r.getVert 1) ∈ c.edges ∨
      s(r.getVert 0, r.getVert 1) ∈ p.edges) := fun _ => hredge1
  have hqre : M = 1 → ¬ (s((fun k => r.getVert (M - k)) 0, (fun k => r.getVert (M - k)) 1) ∈
      c.edges ∨ s((fun k => r.getVert (M - k)) 0, (fun k => r.getVert (M - k)) 1) ∈ p.edges) := by
    intro hM
    show ¬ (s(r.getVert (M - 0), r.getVert (M - 1)) ∈ c.edges ∨
      s(r.getVert (M - 0), r.getVert (M - 1)) ∈ p.edges)
    rw [show M - 0 = 1 from by omega, show M - 1 = 0 from by omega, Sym2.eq_swap]
    exact hredge1
  -- what the vertices of `C₁ ∪ P₁` look like
  have hSdesc : ∀ z : V, (z ∈ c.support ∨ z ∈ p.support) →
      z = u ∨ z = w ∨ ∃ t, t ≤ L ∧ p.getVert t = z := by
    intro z hz
    rcases hz with hz | hz
    · rcases hcsup z hz with h | h | h | h
      · exact Or.inr (Or.inr ⟨0, by omega, by rw [p.getVert_zero, h]⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨L, le_refl L, by rw [p.getVert_length, h]⟩)
      · exact Or.inr (Or.inl h)
    · obtain ⟨n, hn, hnL⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
      exact Or.inr (Or.inr ⟨n, hnL, hn⟩)
  -- an arc middle joined to a vertex of `P₁`: Rubin's cases (iii) and (iv)
  have hmidp : ∀ (e e' : V) (R : ℕ → V) (t : ℕ),
      (e = u ∧ e' = w) ∨ (e = w ∧ e' = u) → G.Adj a e → G.Adj e b → G.Adj a e' →
      G.Adj e' b → e ≠ e' → s(a, e) ∈ c.edges → s(e, b) ∈ c.edges →
      R 0 = e → R M = p.getVert t → t ≤ L →
      (∀ j, j < M → G.Adj (R j) (R (j + 1))) →
      (∀ j j', j ≤ M → j' ≤ M → R j = R j' → j = j') →
      (∀ j, 0 < j → j < M → R j ≠ a ∧ R j ≠ u ∧ R j ≠ b ∧ R j ≠ w ∧
        ∀ s, s ≤ L → R j ≠ p.getVert s) →
      (M = 1 → ¬ (s(R 0, R 1) ∈ c.edges ∨ s(R 0, R 1) ∈ p.edges)) → False := by
    intro e e' R t hee hae heb hae' he'b hee' hcae hceb hR0 hRM htL hRadj hRinj hRdata hRe
    have hdata' : ∀ j, 0 < j → j < M → R j ≠ a ∧ R j ≠ e ∧ R j ≠ b ∧ R j ≠ e' ∧
        ∀ s, s ≤ L → R j ≠ p.getVert s := by
      intro j hj0 hjM
      obtain ⟨d1, d2, d3, d4, d5⟩ := hRdata j hj0 hjM
      rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨d1, d2, d3, d4, d5⟩
      · exact ⟨d1, d4, d3, d2, d5⟩
    have hpe : ∀ s, 0 < s → s < L → p.getVert s ≠ e := by
      intro s h1 h2
      rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpu s h1 h2
      · exact hpw s h1 h2
    have hpe' : ∀ s, 0 < s → s < L → p.getVert s ≠ e' := by
      intro s h1 h2
      rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpw s h1 h2
      · exact hpu s h1 h2
    rcases (by omega : t = 0 ∨ t = L ∨ (0 < t ∧ t < L)) with rfl | rfl | ⟨ht0, htL'⟩
    · -- Rubin's case (iv), at the branch vertex `a`
      have hM2 : 2 ≤ M := by
        rcases (by omega : M = 1 ∨ 2 ≤ M) with hM | hM
        · exfalso
          refine hRe hM (Or.inl ?_)
          rw [hR0, show (1 : ℕ) = M from hM.symm, hRM, p.getVert_zero, Sym2.eq_swap]
          exact hcae
        · exact hM
      exact case_mixed hae heb hae' he'b hab hee' hM2 hR0
        (by rw [hRM, p.getVert_zero]) hRadj hRinj
        (fun j h1 h2 => ⟨(hdata' j h1 h2).1, (hdata' j h1 h2).2.1, (hdata' j h1 h2).2.2.1,
          (hdata' j h1 h2).2.2.2.1⟩) hch
    · -- Rubin's case (iv), at the branch vertex `b`
      have hM2 : 2 ≤ M := by
        rcases (by omega : M = 1 ∨ 2 ≤ M) with hM | hM
        · exfalso
          refine hRe hM (Or.inl ?_)
          rw [hR0, show (1 : ℕ) = M from hM.symm, hRM, p.getVert_length]
          exact hceb
        · exact hM
      exact case_mixed heb.symm hae.symm he'b.symm hae'.symm hab.symm hee' hM2 hR0
        (by rw [hRM, p.getVert_length]) hRadj hRinj
        (fun j h1 h2 => ⟨(hdata' j h1 h2).2.2.1, (hdata' j h1 h2).2.1, (hdata' j h1 h2).1,
          (hdata' j h1 h2).2.2.2.1⟩) hch
    · -- Rubin's case (iii)
      exact case_interior hae heb hae' he'b hab hee' hParm hl2 hpe hpe' ht0 htL' hM1 hR0 hRM
        hRadj hRinj hdata' hch
  -- the six cases
  rcases hSdesc x₂ hx₂S with hx | hx | ⟨sx, hsxL, hsx⟩ <;>
    rcases hSdesc y₂ hy₂S with hy | hy | ⟨sy, hsyL, hsy⟩
  · exact hx₂y₂ (hx.trans hy.symm)
  · -- Rubin's case (vi)
    exact case_middles hau hub haw hwb hab huw hParm hl2 hpu hpw hM1 (hqf0.trans hx)
      (hqfM.trans hy) hqfadj hrinj hqf hch
  · exact hmidp u w r.getVert sy (Or.inl ⟨rfl, rfl⟩) hau hub haw hwb huw heau heub (hqf0.trans hx)
      (hqfM.trans hsy.symm) hsyL hqfadj hrinj hqf hqfe
  · -- Rubin's case (vi), the other orientation
    exact case_middles hau hub haw hwb hab huw hParm hl2 hpu hpw hM1 (hqr0.trans hy)
      (hqrM.trans hx) hqradj hqrinj hqr hch
  · exact hx₂y₂ (hx.trans hy.symm)
  · exact hmidp w u r.getVert sy (Or.inr ⟨rfl, rfl⟩) haw hwb hau hub (Ne.symm huw) heaw hewb
      (hqf0.trans hx)
      (hqfM.trans hsy.symm) hsyL hqfadj hrinj hqf hqfe
  · exact hmidp u w (fun k => r.getVert (M - k)) sx (Or.inl ⟨rfl, rfl⟩) hau hub haw hwb huw
      heau heub
      (hqr0.trans hy) (hqrM.trans hsx.symm) hsxL hqradj hqrinj hqr hqre
  · exact hmidp w u (fun k => r.getVert (M - k)) sx (Or.inr ⟨rfl, rfl⟩) haw hwb hau hub
      (Ne.symm huw) heaw hewb
      (hqr0.trans hy) (hqrM.trans hsx.symm) hsxL hqradj hqrinj hqr hqre
  · -- both ends on `P₁`
    have hne : sx ≠ sy := by
      rintro rfl; exact hx₂y₂ (hsx.symm.trans hsy)
    -- normalize so that the smaller index comes first
    have main : ∀ (R : ℕ → V) (α β : ℕ), α < β → β ≤ L → R 0 = p.getVert α →
        R M = p.getVert β →
        (∀ j, j < M → G.Adj (R j) (R (j + 1))) →
        (∀ j j', j ≤ M → j' ≤ M → R j = R j' → j = j') →
        (∀ j, 0 < j → j < M → R j ≠ a ∧ R j ≠ u ∧ R j ≠ b ∧ R j ≠ w ∧
          ∀ s, s ≤ L → R j ≠ p.getVert s) →
        (M = 1 → ¬ (s(R 0, R 1) ∈ c.edges ∨ s(R 0, R 1) ∈ p.edges)) → False := by
      intro R α β hαβ hβL hR0 hRM hRadj hRinj hRdata hRe
      have hdm : 3 ≤ (β - α) + M := by
        rcases (by omega : β - α = 1 ∧ M = 1 ∨ 3 ≤ (β - α) + M) with ⟨hd, hM⟩ | h
        · exfalso
          refine hRe hM (Or.inr ?_)
          rw [hR0, show (1 : ℕ) = M from hM.symm, hRM, show β = α + 1 from by omega]
          exact getVert_mem_edges p (by omega)
        · exact h
      rcases (by omega : α = 0 ∧ β = L ∨ β < L ∨ (0 < α ∧ β = L)) with ⟨rfl, rfl⟩ | hlt | ⟨hα, rfl⟩
      · -- Rubin's case (v)
        exact case_branches hau hub haw hwb hab huw hParm hl2 hpu hpw hM1
          (by rw [hR0, p.getVert_zero]) (by rw [hRM, p.getVert_length]) hRadj hRinj hRdata hch
      · exact case_onP1 hau hub haw hwb hab huw hParm hl2 hpu hpw hαβ hlt hM1 hR0 hRM hRadj
          hRinj hRdata hdm hch
      · -- reverse the whole configuration so that the second end is not `b`
        refine case_onP1 (a := b) (b := a) (p := fun j => p.getVert (L - j))
          (q := fun j => R (M - j)) (α := 0) (β := L - α) hub.symm hau.symm hwb.symm haw.symm
          hab.symm huw hParm.rev hl2 ?_ ?_ (by omega) (by omega) hM1 ?_ ?_ ?_ ?_ ?_ (by omega) hch
        · exact fun t h1 h2 => hpu (L - t) (by omega) (by omega)
        · exact fun t h1 h2 => hpw (L - t) (by omega) (by omega)
        · show R (M - 0) = p.getVert (L - 0)
          rw [Nat.sub_zero, Nat.sub_zero]; exact hRM
        · show R (M - M) = p.getVert (L - (L - α))
          rw [Nat.sub_self, show L - (L - α) = α from by omega]; exact hR0
        · intro j hj
          show G.Adj (R (M - j)) (R (M - (j + 1)))
          have := hRadj (M - (j + 1)) (by omega)
          rw [show M - (j + 1) + 1 = M - j from by omega] at this
          exact this.symm
        · intro j j' hj hj' he
          have he' : R (M - j) = R (M - j') := he
          have := hRinj (M - j) (M - j') (by omega) (by omega) he'
          omega
        · intro j hj0 hjM
          obtain ⟨d1, d2, d3, d4, d5⟩ := hRdata (M - j) (by omega) (by omega)
          exact ⟨d3, d2, d1, d4, fun t ht => d5 (L - t) (by omega)⟩
    rcases (by omega : sx < sy ∨ sy < sx) with h | h
    · exact main r.getVert sx sy h hsyL (hqf0.trans hsx.symm) (hqfM.trans hsy.symm) hqfadj hrinj
        hqf hqfe
    · exact main (fun k => r.getVert (M - k)) sy sx h hsxL (hqr0.trans hsy.symm)
        (hqrM.trans hsx.symm) hqradj hqrinj hqr hqre


/-! ### Assembly -/

/-- **Rubin's theorem, structural half.** A connected graph of minimum degree `≥ 2` that is
`2`-choosable is either an even cycle or `θ_{2,2,2m}`: its edges are exactly those of a single
even cycle, or exactly those of a four-cycle `a, u, b, w` together with a path of even length
`≥ 2` from `a` to `b`, internally disjoint from the cycle and edge-disjoint from it. In the
second case the two branch vertices `a`, `b` are opposite corners of the four-cycle, the other
two corners being `u` and `w`.

Due to A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West
Coast Conf. on Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congr.
Numer. **26**, Utilitas Math., Winnipeg, **1980**, 125–157, pp. 131–134. Nothing here is claimed
as new; only the proof is written out.

The conclusion is stated as data about walks rather than as an isomorphism, so that the two
isomorphism constructions — `closePath k` from a connected `2`-regular graph, and `theta m` from
`C₁ ∪ P₁` — can consume it separately. -/
theorem rubin_structure (hconn : G.Connected) (hdeg : ∀ z : V, 2 ≤ G.degree z)
    (hch : G.Choosable 2) :
    (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Even c.length ∧ (∀ z : V, z ∈ c.support) ∧
        ∀ x y : V, G.Adj x y → s(x, y) ∈ c.edges) ∨
    (∃ (v : V) (c : G.Walk v v) (a b u w : V) (p : G.Walk a b), c.IsCycle ∧ c.length = 4 ∧
      a ∈ c.support ∧ b ∈ c.support ∧ a ≠ b ∧ u ≠ w ∧
      G.Adj a u ∧ G.Adj u b ∧ G.Adj a w ∧ G.Adj w b ∧
      (∀ z, z ∈ c.support → z = a ∨ z = u ∨ z = b ∨ z = w) ∧
      p.IsPath ∧ Even p.length ∧ 2 ≤ p.length ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support) ∧ (∀ e ∈ p.edges, e ∉ c.edges) ∧
      (∀ z : V, z ∈ c.support ∨ z ∈ p.support) ∧
      ∀ x y : V, G.Adj x y → s(x, y) ∈ c.edges ∨ s(x, y) ∈ p.edges) := by
  classical
  have hnb : ∀ z : V, ∃ y : V, G.Adj z y := fun z =>
    (G.degree_pos_iff_exists_adj z).mp (by have := hdeg z; omega)
  obtain ⟨v, c, hc, hmin⟩ := exists_shortest_isCycle hconn hdeg
  by_cases hedge : ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ c.edges
  · obtain ⟨a, b, p, ha, hb, hab, hp, hp1, hpint, hpedge⟩ :=
      exists_connecting_path_of_cycle_of_choosable hconn hdeg hch hc hedge
    obtain ⟨u, w, hlen4, hev, hl2, hau, hub, haw, hwb, huw, hua, hub2, hwa, hwb2,
      heau, heub, heaw, hewb, hcsup⟩ := step4 hch hc hmin ha hb hab hp hpint hpedge
    by_cases hmore : ∃ x y : V, G.Adj x y ∧ ¬ (s(x, y) ∈ c.edges ∨ s(x, y) ∈ p.edges)
    · exact (step56 hconn hdeg hch hc hab hp hpint hl2 hau hub haw hwb huw heau heub heaw
        hewb hcsup hmore).elim
    · have hall : ∀ x y : V, G.Adj x y → s(x, y) ∈ c.edges ∨ s(x, y) ∈ p.edges := by
        intro x y hxy
        by_contra hcon
        exact hmore ⟨x, y, hxy, hcon⟩
      refine Or.inr ⟨v, c, a, b, u, w, p, hc, hlen4, ha, hb, hab, huw, hau, hub, haw, hwb,
        hcsup, hp, hev, hl2, hpint, hpedge, ?_, hall⟩
      intro z
      obtain ⟨y, hzy⟩ := hnb z
      rcases hall z y hzy with h | h
      · exact Or.inl (c.fst_mem_support_of_mem_edges h)
      · exact Or.inr (p.fst_mem_support_of_mem_edges h)
  · push Not at hedge
    refine Or.inl ⟨v, c, hc, ?_, fun z => ?_, hedge⟩
    · have h3 := hc.three_le_length
      have hodd : ¬ Even (c.length - 1) := fun hE =>
        not_choosable_two_of_odd_closed_walk hE c.getVert (fun i hi => cycleWalk_adj c hi)
          (cycleWalk_closes hc) hch
      rcases Nat.even_or_odd (c.length - 1) with h | h
      · exact absurd h hodd
      · obtain ⟨k, hk⟩ := h
        exact ⟨k + 1, by omega⟩
    · obtain ⟨y, hzy⟩ := hnb z
      exact c.fst_mem_support_of_mem_edges (hedge z y hzy)

#print axioms ListColoring.gArmOf_gsize_take_add
#print axioms ListColoring.gDecode
#print axioms ListColoring.armStepB_iff
#print axioms ListColoring.gAdjAux_iff
#print axioms ListColoring.gAdjB_iff
#print axioms ListColoring.contains_gtheta_of_arms
#print axioms ListColoring.contains_gtheta_of_armFam
#print axioms ListColoring.contains_gtheta_three
#print axioms ListColoring.contains_gtheta_four
#print axioms ListColoring.isArm_of_walk
#print axioms ListColoring.armsDisj_of_walks
#print axioms ListColoring.contains_gtheta_of_walks
#print axioms ListColoring.not_choosable_two_of_three_arms
#print axioms ListColoring.not_choosable_two_of_arm_one
#print axioms ListColoring.not_choosable_two_of_four_arms
#print axioms ListColoring.getVert_mem_edges
#print axioms ListColoring.exists_arcs_of_cycle
#print axioms ListColoring.exists_isCycle_four
#print axioms ListColoring.step4
#print axioms ListColoring.isArm_edge
#print axioms ListColoring.isArm_two
#print axioms ListColoring.isArm_three
#print axioms ListColoring.IsArm.inj_all
#print axioms ListColoring.IsArm.rev
#print axioms ListColoring.case_branches
#print axioms ListColoring.case_middles
#print axioms ListColoring.case_mixed
#print axioms ListColoring.case_interior
#print axioms ListColoring.case_onP1
#print axioms ListColoring.step56
#print axioms ListColoring.rubin_structure

end ListColoring
