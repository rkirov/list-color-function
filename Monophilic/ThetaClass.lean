/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.RubinHard

/-!
# The classification of `2`-choosable theta graphs

`Monophilic.RubinHard` reduces Rubin's hard direction to two named hypotheses, one purely
structural (`Monophilic.ThetaAlternative`) and one the classification of `2`-choosable *theta*
graphs (`Monophilic.ThetaClassification`). This file **discharges the second**:

> `θ_{a,b,c}` of a valid shape is `2`-choosable if and only if the shape is `(2, 2, \text{even})`.

Only the forward implication is a loan; it is proved here in the form
`Monophilic.not_choosable_two_thetaGen`, and `Monophilic.thetaClassification` is the resulting
term of type `Monophilic.ThetaClassification`. Consequently
`Monophilic.rubinFamily_of_choosable'`, `Monophilic.choosable_two_iff_rubinFamily'` and
`Monophilic.choosable_two_pendantTower_iff'` need only `ThetaAlternative`.

## The argument

`Monophilic.thetaBadLists` gives both branch vertices the list `{1, 2}`, so a coloring of
`θ_{a,b,c}` from it consists of a pair `(α, β) ∈ {1,2} × {1,2}` of branch colors together with a
coloring of the interior of each arm; an arm **blocks** `(α, β)` when its lists leave no interior
coloring compatible with `α` and `β`. `RubinHard` checks by brute force that the four pairs are
all blocked for every valid non-Rubin shape with `a ≤ 4`, `b ≤ 4`, `c ≤ 5`. What was missing, and
is supplied here, is the induction along an arm of **unbounded** length. It comes in two shapes,
both consequences of one alternating-chain lemma:

* `Monophilic.const_block` — an arm whose interior lists are all `{1, 2}` forces its two ends to
  alternate, so a coloring exists exactly when `α = β` agrees with the parity of the number `m` of
  interior vertices: `α = β ↔ m` odd. Such an arm therefore blocks **two** pairs, one diagonal or
  the other according to that parity.
* `Monophilic.armBlockLists_forced` — an arm with `m ≥ 2` interior vertices carrying the lists
  `Monophilic.armBlockLists α₀ β₀ m` propagates a forced chain: if its first interior vertex avoids
  `α₀` — which it must when `α = α₀` — then its last interior vertex is forced to the color `β₀`.
  Such an arm blocks the single pair `(α₀, β₀)`.

For a valid shape other than `(2, 2, \text{even})` one of two things happens. If `b = 2` then
`a ≤ 2`, the three arm lengths do not all have the same parity, and two applications of
`const_block` already contradict each other — this is the odd-cycle case, and no coloring of the
constant lists `{1, 2}` exists at all. Otherwise `3 ≤ b ≤ c`: the first arm splits the four pairs
into two by parity through `const_block`, and the two long arms block the two survivors through
`armBlockLists_forced`.

The whole analysis is carried out on **indices** rather than on `Fin (a+b+c-1)`: a coloring `f` of
`θ_{a,b,c}` is read as a function `F : ℕ → ℕ`, the lists as `Monophilic.badListAt`, and the arms
as the three ranges of indices that `Monophilic.armStepB` links up.

## Main definitions

* `Monophilic.badListAt` : `Monophilic.thetaBadLists` as a function of the index of a vertex
* `Monophilic.thetaGenToTheta` : the embedding of `thetaGen 2 2 (2m)` into `Monophilic.theta m`

## Main results

* `Monophilic.alt_chain` : **the alternating chain** — a stretch of a path whose lists are all
  `{p, q}` alternates, and is determined by the color at either end
* `Monophilic.const_block` : **which pairs an arm with constant lists blocks**
* `Monophilic.armBlockLists_forced` : **the forced chain along a blocking arm**
* `Monophilic.card_thetaBadLists` : the witness is a `2`-list assignment, for every shape
* `Monophilic.col_thetaBadLists_eq_zero` : **the witness has no coloring at all**, for every valid
  non-Rubin shape
* `Monophilic.not_choosable_two_thetaGen` : **`θ_{a,b,c}` is not `2`-choosable** unless its shape
  is `(2, 2, \text{even})`
* `Monophilic.thetaClassification` : **`Monophilic.ThetaClassification`, discharged**
* `Monophilic.thetaGenToTheta` : the embedding of `thetaGen 2 2 (2m)` into `Monophilic.theta m`,
  and `Monophilic.choosable_two_thetaGen_of_goodShape` : **Rubin's own shape is `2`-choosable** on
  the general model
* `Monophilic.choosable_two_thetaGen_iff` : **the classification as an `↔`**
* `Monophilic.rubinFamily_of_choosable'`, `Monophilic.choosable_two_iff_rubinFamily'`,
  `Monophilic.choosable_two_pendantTower_iff'` : Rubin's theorem relative to
  `Monophilic.ThetaAlternative` alone
-/

open Finset

namespace Monophilic

open SimpleGraph

set_option maxRecDepth 100000

/-! ### Numerical checks

Every claim below is checked by brute force on concrete shapes before it is proved. The first
sweep is the content of `Monophilic.const_block`: with the constant lists `{1, 2}` the theta graph
has a coloring exactly when its three arm lengths all have the same parity — otherwise it has an
odd cycle. The second extends the sweep of `Monophilic.thetaBadCheck` past the range recorded in
`Monophilic.RubinHard`. -/

section Guards

-- `col(θ_{a,b,c}, {1,2}) = 0` exactly when the three lengths are not all of the same parity.
#guard [1, 2, 3, 4].all fun a => [2, 3, 4].all fun b => [2, 3, 4, 5].all fun c =>
  if decide (1 ≤ a ∧ a ≤ b ∧ b ≤ c) then
    (((thetaGen a b c).col (fun _ => ({1, 2} : Finset ℕ)) == 0) ==
      !(decide (a % 2 = b % 2 ∧ b % 2 = c % 2)))
  else true

-- The uniform witness still works past the range swept in `Monophilic.RubinHard`.
#guard thetaBadCheck 4 5 6
#guard thetaBadCheck 5 5 5
#guard thetaBadCheck 3 3 7
#guard thetaBadCheck 1 5 5

-- and it still fails, as it must, on Rubin's own shape.
#guard colThetaBad 2 2 8 = 2

end Guards

/-! ### Alternating chains -/

/-- **The alternating chain.** Along a stretch `k, k+1, …, m-1` of a path all of whose lists are
contained in the two-element set `{p, q}`, the colors alternate: knowing the color at the first
position `k` determines the color everywhere, as `q` at even distance and `p` at odd distance.

This is the one induction behind both `Monophilic.const_block` and
`Monophilic.armBlockLists_forced`, and hence behind the whole classification. The stretch is
indexed by natural numbers rather than by vertices of a path, so that it applies verbatim to an
arm of a theta graph, whose interior is a block of consecutive indices. -/
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

/-- **Constant lists alternate.** The special case of `Monophilic.alt_chain` in which every list
is `{1, 2}`: a coloring of such a stretch is determined by the color it gives to the first
position, and the other color is `3 - g 0`. -/
theorem const_chain (g : ℕ → ℕ) {m : ℕ}
    (hg : ∀ j, j < m → g j = 1 ∨ g j = 2)
    (hne : ∀ j, j + 1 < m → g j ≠ g (j + 1)) :
    ∀ i, i < m → g i = if i % 2 = 0 then g 0 else 3 - g 0 := by
  intro i hi
  have h := alt_chain (p := 3 - g 0) (q := g 0) g 0 m
    (fun j _ hj => by have := hg j hj; have := hg 0 (by omega); omega) hne rfl i (by omega)
  simpa using h

/-- **The forced chain along a blocking arm.** This is the induction along an arm of unbounded
length that turns `Monophilic.armBlockLists` from a witness into a proof.

An arm with `m ≥ 2` interior vertices carrying the lists `armBlockLists α β m` starts with the
list `{α, 3}`; if its first interior vertex avoids `α` it must therefore take the color `3`, and
from there the coloring is forced all the way along — alternating `3, β, 3, …` when `m` is even,
and `3, 4, β, 3, β, …` when `m` is odd, the detour through the auxiliary color `4` correcting the
parity. Either way the last interior vertex is forced to `β`, so it cannot avoid it: the arm
blocks the pair `(α, β)` of branch colors, and only that pair. -/
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

/-- **An arm with constant lists `{1, 2}` blocks exactly one of the two diagonals.** Its `m`
interior vertices alternate, so the two colors it leaves at its two ends are equal when `m` is
odd — and then the two branch colors must agree — and different when `m` is even. The degenerate
case `m = 0`, an arm which is a single edge joining the two branch vertices, is covered by `hd`
and falls on the even side.

In terms of the length `ℓ = m + 1` of the arm: a coloring exists exactly when `α = β` agrees with
"`ℓ` is even". So an arm of *even* length blocks the two pairs `(1,2)` and `(2,1)`, and an arm of
*odd* length blocks `(1,1)` and `(2,2)`. -/
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

/-- `Monophilic.thetaBadLists` read as a function of the *index* of the vertex. The whole
analysis below runs on indices, `Monophilic.thetaBadLists_apply` being the (definitional) bridge
back to the vertices of `Monophilic.TGV`. -/
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

-- `badListAt` really is `thetaBadLists` read on indices, and the witness has lists of size two.
#guard ∀ v ∈ (univ : Finset (TGV 3 4 5)), thetaBadLists 3 4 5 v = badListAt 3 4 5 v.val
#guard ∀ v ∈ (univ : Finset (TGV 3 4 5)), (thetaBadLists 3 4 5 v).card = 2
#guard ∀ v ∈ (univ : Finset (TGV 1 3 3)), (thetaBadLists 1 3 3 v).card = 2

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


/-! ### The good shape: `θ_{2,2,2m}` on the general model

The remaining direction is Rubin's own family. `Monophilic.choosable_theta` proves that
`Monophilic.theta m` — a path of length `2m` with two extra vertices, each joined to both of its
ends — is `2`-choosable, and `Monophilic.thetaGen 2 2 (2 * m)` is the same graph on
`Fin (2m + 3)`. Rather than build an isomorphism, it is enough to **embed** the second in the
first, since `SimpleGraph.Choosable.comap` transports choosability backwards along an injection
carrying edges to edges. The embedding sends the index `0` to the outer apex, the index `1` to the
inner one, the two branch vertices `2m+1` and `2m+2` to the two terminal vertices of the long
path, and an index `2 ≤ i ≤ 2m` to the vertex `pathVtx (2m) (i - 1)` of its interior. -/

/-- The position along the long path of `Monophilic.theta m` taken by the vertex of `θ_{2,2,2m}`
of index `i`, for `2 ≤ i`: the two branch vertices `2m+1` and `2m+2` go to the two ends `0` and
`2m`, and an interior index `i` goes to `i - 1`. -/
private def tgIdx (m i : ℕ) : ℕ :=
  if i = 2 * m + 1 then 0 else if i = 2 * m + 2 then 2 * m else i - 1

/-- **The embedding of `thetaGen 2 2 (2m)` into `Monophilic.theta m`.** It is in fact a bijection —
the two graphs are the same theta graph on differently named vertices — but only injectivity and
edge preservation are needed, since `SimpleGraph.Choosable.comap` transports choosability
backwards along such a map. -/
def thetaGenToTheta (m : ℕ) (v : TGV 2 2 (2 * m)) : ThetaV m :=
  if v.val = 0 then none
  else if v.val = 1 then some none
  else if v.val = 2 * m + 1 then some (some (pathEnd (2 * m)))
  else if v.val = 2 * m + 2 then some (some (pathStart (2 * m)))
  else some (some (pathVtx (2 * m) (v.val - 1)))

-- The embedding is injective and carries edges to edges, on the two smallest members.
#guard ((univ : Finset (TGV 2 2 (2 * 1))).image (thetaGenToTheta 1)).card
  = Fintype.card (TGV 2 2 (2 * 1))
#guard ((univ : Finset (TGV 2 2 (2 * 2))).image (thetaGenToTheta 2)).card
  = Fintype.card (TGV 2 2 (2 * 2))
#guard ∀ v ∈ (univ : Finset (TGV 2 2 (2 * 2))), ∀ w ∈ (univ : Finset (TGV 2 2 (2 * 2))),
  (thetaGen 2 2 (2 * 2)).Adj v w → (theta 2).Adj (thetaGenToTheta 2 v) (thetaGenToTheta 2 w)

private lemma tgtt_zero (m : ℕ) (u : TGV 2 2 (2 * m)) (hu : u.val = 0) :
    thetaGenToTheta m u = none := by
  simp only [thetaGenToTheta, if_pos hu]

private lemma tgtt_one (m : ℕ) (u : TGV 2 2 (2 * m)) (hu : u.val = 1) :
    thetaGenToTheta m u = some none := by
  simp only [thetaGenToTheta, if_neg (show ¬ (u.val = 0) from by omega), if_pos hu]

private lemma tgtt_S (m : ℕ) (hm : 1 ≤ m) (u : TGV 2 2 (2 * m)) (hu : u.val = 2 * m + 1) :
    thetaGenToTheta m u = some (some (pathEnd (2 * m))) := by
  simp only [thetaGenToTheta, if_neg (show ¬ (u.val = 0) from by omega),
    if_neg (show ¬ (u.val = 1) from by omega), if_pos hu]

private lemma tgtt_T (m : ℕ) (u : TGV 2 2 (2 * m)) (hu : u.val = 2 * m + 2) :
    thetaGenToTheta m u = some (some (pathStart (2 * m))) := by
  simp only [thetaGenToTheta, if_neg (show ¬ (u.val = 0) from by omega),
    if_neg (show ¬ (u.val = 1) from by omega), if_neg (show ¬ (u.val = 2 * m + 1) from by omega),
    if_pos hu]

private lemma tgtt_mid (m : ℕ) (u : TGV 2 2 (2 * m)) (h2 : 2 ≤ u.val) (h3 : u.val ≤ 2 * m) :
    thetaGenToTheta m u = some (some (pathVtx (2 * m) (u.val - 1))) := by
  simp only [thetaGenToTheta, if_neg (show ¬ (u.val = 0) from by omega),
    if_neg (show ¬ (u.val = 1) from by omega), if_neg (show ¬ (u.val = 2 * m + 1) from by omega),
    if_neg (show ¬ (u.val = 2 * m + 2) from by omega)]

private lemma tgtt_idx (m : ℕ) (hm : 1 ≤ m) (u : TGV 2 2 (2 * m)) (h2 : 2 ≤ u.val) :
    thetaGenToTheta m u = some (some (pathVtx (2 * m) (tgIdx m u.val))) := by
  have hu := u.isLt
  rcases (show u.val = 2 * m + 1 ∨ u.val = 2 * m + 2 ∨ u.val ≤ 2 * m from by omega) with h | h | h
  · rw [tgtt_S m hm u h, tgIdx, if_pos h, pathVtx_zero]
  · rw [tgtt_T m u h, tgIdx, if_neg (show ¬ (u.val = 2 * m + 1) from by omega), if_pos h,
      pathVtx_last]
  · rw [tgtt_mid m u h2 h, tgIdx, if_neg (show ¬ (u.val = 2 * m + 1) from by omega),
      if_neg (show ¬ (u.val = 2 * m + 2) from by omega)]

/-- The embedding is injective: distinct indices land on distinct positions along the long path. -/
theorem thetaGenToTheta_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (thetaGenToTheta m) := by
  have hidx : ∀ i : ℕ, 2 ≤ i → i < 2 * m + 3 → tgIdx m i ≤ 2 * m := by
    intro i h2 h3
    simp only [tgIdx]
    split_ifs <;> omega
  intro v w h
  refine Fin.val_injective ?_
  have hv := v.isLt
  have hw := w.isLt
  rcases (show v.val = 0 ∨ v.val = 1 ∨ 2 ≤ v.val from by omega) with hv' | hv' | hv' <;>
    rcases (show w.val = 0 ∨ w.val = 1 ∨ 2 ≤ w.val from by omega) with hw' | hw' | hw'
  · omega
  · rw [tgtt_zero m v hv', tgtt_one m w hw'] at h; simp at h
  · rw [tgtt_zero m v hv', tgtt_idx m hm w hw'] at h; simp at h
  · rw [tgtt_one m v hv', tgtt_zero m w hw'] at h; simp at h
  · omega
  · rw [tgtt_one m v hv', tgtt_idx m hm w hw'] at h; simp at h
  · rw [tgtt_idx m hm v hv', tgtt_zero m w hw'] at h; simp at h
  · rw [tgtt_idx m hm v hv', tgtt_one m w hw'] at h; simp at h
  · rw [tgtt_idx m hm v hv', tgtt_idx m hm w hw'] at h
    have h2 : pathVtx (2 * m) (tgIdx m v.val) = pathVtx (2 * m) (tgIdx m w.val) := by simpa using h
    have h3 := pathVtx_inj (2 * m) _ _ (hidx v.val hv' (by omega)) (hidx w.val hw' (by omega)) h2
    simp only [tgIdx] at h3
    split_ifs at h3 <;> omega

private lemma theta_adj_path (m : ℕ) {u u' : PathV (2 * m)} (h : (pathG (2 * m)).Adj u u') :
    (theta m).Adj (some (some u)) (some (some u')) := h

private lemma theta_adj_inner (m : ℕ) {u : PathV (2 * m)}
    (hu : u ∈ ({pathStart (2 * m), pathEnd (2 * m)} : Finset (PathV (2 * m)))) :
    (theta m).Adj (some none) (some (some u)) := hu

private lemma theta_adj_outer (m : ℕ) {x : Option (PathV (2 * m))}
    (hx : x ∈ ({some (pathStart (2 * m)), some (pathEnd (2 * m))} :
      Finset (Option (PathV (2 * m))))) :
    (theta m).Adj none (some x) := hx

/-- The edges of `θ_{2,2,2m}` in the general model, spelled out. -/
private lemma thetaGenAdjB_decode (m : ℕ) (hm : 1 ≤ m) {x y : ℕ}
    (h : thetaGenAdjB 2 2 (2 * m) x y = true) :
    (x = 2 * m + 1 ∧ y = 0) ∨ (x = 0 ∧ y = 2 * m + 2) ∨ (x = 2 * m + 1 ∧ y = 1) ∨
      (x = 1 ∧ y = 2 * m + 2) ∨ (2 ≤ x ∧ x ≤ 2 * m - 1 ∧ y = x + 1) ∨
      (x = 2 * m + 1 ∧ y = 2) ∨ (x = 2 * m ∧ y = 2 * m + 2) := by
  simp only [thetaGenAdjB, armStepB, if_neg (show ¬ ((2 : ℕ) - 1 = 0) from by omega),
    if_neg (show ¬ (2 * m - 1 = 0) from by omega), Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with (((h | h) | h) | ((h | h) | h)) | ((h | h) | h) <;> omega

private lemma thetaGenToTheta_adjB (m : ℕ) (hm : 1 ≤ m) (v w : TGV 2 2 (2 * m))
    (h : thetaGenAdjB 2 2 (2 * m) v.val w.val = true) :
    (theta m).Adj (thetaGenToTheta m v) (thetaGenToTheta m w) := by
  have hv := v.isLt
  have hw := w.isLt
  rcases thetaGenAdjB_decode m hm h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [tgtt_S m hm v h1, tgtt_zero m w h2]
    exact (theta_adj_outer m (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).symm
  · rw [tgtt_zero m v h1, tgtt_T m w h2]
    exact theta_adj_outer m (Finset.mem_insert_self _ _)
  · rw [tgtt_S m hm v h1, tgtt_one m w h2]
    exact (theta_adj_inner m (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).symm
  · rw [tgtt_one m v h1, tgtt_T m w h2]
    exact theta_adj_inner m (Finset.mem_insert_self _ _)
  · rw [tgtt_mid m v h1 (by omega), tgtt_mid m w (by omega) (by omega)]
    exact theta_adj_path m
      ((pathG_adj_pathVtx (2 * m) (v.val - 1) (w.val - 1) (by omega) (by omega)).mpr
        (Or.inl (by omega)))
  · rw [tgtt_S m hm v h1, tgtt_mid m w (by omega) (by omega), ← pathVtx_zero (2 * m)]
    exact theta_adj_path m
      ((pathG_adj_pathVtx (2 * m) 0 (w.val - 1) (by omega) (by omega)).mpr (Or.inl (by omega)))
  · rw [tgtt_mid m v (by omega) (by omega), tgtt_T m w h2, ← pathVtx_last (2 * m)]
    exact theta_adj_path m
      ((pathG_adj_pathVtx (2 * m) (v.val - 1) (2 * m) (by omega) (by omega)).mpr
        (Or.inl (by omega)))

/-- The embedding carries edges to edges. -/
theorem thetaGenToTheta_adj (m : ℕ) (hm : 1 ≤ m) (v w : TGV 2 2 (2 * m))
    (h : (thetaGen 2 2 (2 * m)).Adj v w) :
    (theta m).Adj (thetaGenToTheta m v) (thetaGenToTheta m w) := by
  rcases h.2 with hb | hb
  · exact thetaGenToTheta_adjB m hm v w hb
  · exact (thetaGenToTheta_adjB m hm w v hb).symm

/-- **`θ_{2,2,2m}` is `2`-choosable in the general model**, for every `m ≥ 1`: it embeds into
`Monophilic.theta m`, and `Monophilic.choosable_theta` applies. -/
theorem choosable_two_thetaGen_two_two (m : ℕ) (hm : 1 ≤ m) :
    (thetaGen 2 2 (2 * m)).Choosable 2 :=
  Choosable.comap (choosable_theta m hm) (thetaGenToTheta_injective m hm)
    (fun x y hxy => thetaGenToTheta_adj m hm x y hxy)

/-- **A theta graph of Rubin's shape is `2`-choosable.** -/
theorem choosable_two_thetaGen_of_goodShape {a b c : ℕ} (hv : ValidShape a b c)
    (hg : GoodShape a b c) : (thetaGen a b c).Choosable 2 := by
  obtain ⟨ha, hab, hbc, hb2⟩ := hv
  obtain ⟨rfl, rfl, hc⟩ := hg
  obtain ⟨r, hr⟩ := hc
  obtain ⟨m, rfl⟩ : ∃ m, c = 2 * m := ⟨r, by omega⟩
  exact choosable_two_thetaGen_two_two m (by omega)

/-- **The classification of `2`-choosable theta graphs, as an `↔`**: a theta graph of a valid shape
is `2`-choosable exactly when its shape is `(2, 2, \text{even})`. -/
theorem choosable_two_thetaGen_iff {a b c : ℕ} (hv : ValidShape a b c) :
    (thetaGen a b c).Choosable 2 ↔ GoodShape a b c :=
  ⟨fun h => by
      by_contra hg
      exact not_choosable_two_thetaGen hv hg h,
    choosable_two_thetaGen_of_goodShape hv⟩

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

/-! ### Cross-checks

The general theorems specialize to the explicit cases proved by hand in `Monophilic.RubinHard`,
and to the two families settled there by other means. -/

section Examples

example : ¬ (thetaGen 1 3 3).Choosable 2 :=
  not_choosable_two_thetaGen ⟨by omega, by omega, by omega, by omega⟩ (by rintro ⟨h, -, -⟩; omega)

example : ¬ (thetaGen 3 3 3).Choosable 2 :=
  not_choosable_two_thetaGen ⟨by omega, by omega, by omega, by omega⟩ (by rintro ⟨h, -, -⟩; omega)

example : ¬ (thetaGen 2 4 4).Choosable 2 :=
  not_choosable_two_thetaGen ⟨by omega, by omega, by omega, by omega⟩ (by rintro ⟨-, h, -⟩; omega)

/-- The family `θ_{2,2,\text{odd}}`, which `Monophilic.not_choosable_two_thetaOf_odd` settles on
the model `Monophilic.thetaOf`, is now available on `Monophilic.thetaGen` as well. -/
example (r : ℕ) : ¬ (thetaGen 2 2 (2 * r + 3)).Choosable 2 :=
  not_choosable_two_thetaGen ⟨by omega, by omega, by omega, by omega⟩
    (by rintro ⟨-, -, h⟩; rw [Nat.even_iff] at h; omega)

/-- Rubin's own family, on the general model. -/
example (r : ℕ) : (thetaGen 2 2 (2 * r + 2)).Choosable 2 :=
  choosable_two_thetaGen_of_goodShape ⟨by omega, by omega, by omega, by omega⟩
    ⟨rfl, rfl, by rw [Nat.even_iff]; omega⟩

end Examples

end Monophilic


#print axioms Monophilic.alt_chain
#print axioms Monophilic.const_chain
#print axioms Monophilic.armBlockLists_forced
#print axioms Monophilic.const_block
#print axioms Monophilic.card_armBlockLists
#print axioms Monophilic.thetaBadLists_apply
#print axioms Monophilic.card_thetaBadLists
#print axioms Monophilic.col_thetaBadLists_eq_zero
#print axioms Monophilic.not_choosable_two_thetaGen
#print axioms Monophilic.thetaGenToTheta_injective
#print axioms Monophilic.thetaGenToTheta_adj
#print axioms Monophilic.choosable_two_thetaGen_two_two
#print axioms Monophilic.choosable_two_thetaGen_of_goodShape
#print axioms Monophilic.choosable_two_thetaGen_iff
#print axioms Monophilic.thetaClassification
#print axioms Monophilic.rubinFamily_of_choosable'
#print axioms Monophilic.choosable_two_iff_rubinFamily'
#print axioms Monophilic.choosable_two_pendantTower_iff'
