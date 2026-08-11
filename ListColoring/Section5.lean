/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.NotChoosable
import ListColoring.ThetaChoosable
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Kirov–Naimi §5: `n`-choosable but not enumeratively chromatic-choosable at `n`

Section 5 of **Kirov–Naimi 2016** constructs, for each list size, a graph that is choosable from
lists of that size and yet is *not* enumeratively chromatic-choosable at it (the paper's "not
`n`-monophilic"). Together with Theorem 1 and Theorem 2 this is what separates the two notions:
choosability is an existence property, enumerative chromatic-choosability a counting one, and
neither implies the other.

## The construction

`K_{n,nⁿ}` — `ListColoring.NotChoosable`, the Erdős–Rubin–Taylor graph — carries a list assignment
`L₀` of `n`-lists with no coloring at all. Renaming its colors out of the way and adding one extra
color `j` to every list gives `Lblock n j`, an `(n+1)`-list assignment on which the copy still
"remembers" `j`: any coloring must use `j` somewhere.

`H n p` is then the paper's `H_{n+1}`: a complete bipartite `K_{n,p}` on vertices `v₁, …, vₙ` and
`w₁, …, w_p`, together with `n²` disjoint copies `G_{i,j}` of `K_{n,nⁿ}`, with each `vᵢ` joined to
every vertex of `G_{i,1}, …, G_{i,n}`.

* **Lemma 7** (`not_ecc`) — under `L`, the color of every `vᵢ` and every `w_k` is forced
  (`coloring_v`, `coloring_w`), so `col(H, L) ≤ x^{n²}` (`col_LH_le`), while the constant list
  admits at least `nᵖ` colorings (`pow_le_colConst`). Choosing `p` large (`exists_pow_lt`) makes the
  constant assignment *not* the minimizer.
* **Lemma 8** (`left_disjoint`, `left_card_eq`) — if `K_{n,nⁿ}` has no coloring from an assignment
  of `n`-lists, the lists on the small side are pairwise disjoint and each has exactly `n` colors.
* **Lemma 9** (`badColor_unique`) — for `(n+1)`-lists on `K_{n,nⁿ}`, at most one color can have the
  property that deleting it destroys every coloring.
* **Lemma 10** (`choosable`) — hence each `vᵢ` has a color that no copy below it objects to, and
  `H_{n+1}` is `(n+1)`-choosable.
* `exists_choosable_not_ecc` is §5's theorem; `exists_choosable_not_ecc_of_two_le` is the statement
  for every list size at once.

## Two places this departs from the paper

**`2 ≤ n` is load-bearing, and the paper's `n ≥ 1` is wrong.** Lemmas 7 and 10 are stated in the
paper "for all `n ≥ 1`", i.e. down to list size `2`. All of Lemmas 7, 9, 10 are false there:

* `p` is defined as the least integer with `nᵖ > x^{n²}`; at `n = 1` that reads `1 > x` with
  `x = col(K_{1,1}, L_j) = 2`, so no such `p` exists and `H₂` is not defined at all.
* Take any `p` regardless: `v₁` is joined to *both* ends of the single edge of `G_{1,1} = K_{1,1}`,
  so `H₂` contains a triangle. Then `col(H₂, 2) = 0 < 2 = col(H₂, L)` — Lemma 7's inequality runs
  the other way — and `H₂`, not being `2`-colorable, is vacuously enumeratively chromatic-choosable
  at `2` and is not `2`-choosable, so Lemma 10 fails too.
* Lemma 9 fails at `n = 1`: `K_{1,1}` with both lists `{0,1}` has *two* colors whose deletion kills
  every coloring.

All three are witnessed by `#guard`s at the end of this file. The paper's conclusion is unharmed:
list size `2` is instead witnessed by `θ_{2,2,4}`, which is `2`-choosable by Rubin
(`ListColoring.choosable_theta`) and not enumeratively chromatic-choosable at `2` by the paper's own
Figure 2 (`ListColoring.not_ecc_theta`). The two together are
`ListColoring.choosable_and_not_ecc_theta`, and that is what `exists_choosable_not_ecc_of_two_le`
uses at `k = 2`.

**Lemma 8 is proved only in the form Lemma 9 consumes.** The paper concludes "`L` is equivalent to
`L₀`" — a bijection of colors together with an automorphism of `K_{n,nⁿ}` carrying one to the other.
Only two consequences of that are ever used, and only those are proved here: the small-side lists
are pairwise disjoint, and each has exactly `n` colors. Likewise `col_LH_le` proves the `≤` of the
paper's `col(H_{n+1}, L) = x^{n²}`, which is the direction Lemma 7 needs.

## Attribution

The mathematics is **Kirov–Naimi 2016, §5** throughout, except for the `n = 1` erratum above and the
`K_{n,nⁿ}` building block, which is **Erdős–Rubin–Taylor 1980**. See `provenance.md`.
-/

open Finset

namespace SimpleGraph
namespace KN5

/-! ### The vertex type of `K_{n,nⁿ}` -/

/-- The vertex type of `K_{n,nⁿ}` as set up in `ListColoring.NotChoosable`: `n` left vertices and
`nⁿ` right vertices indexed by the functions `Fin n → Fin n`. -/
abbrev BV (n : ℕ) : Type := Fin n ⊕ (Fin n → Fin n)

/-! ### Lemma 8 -/

variable {n : ℕ}

/-- If a choice `α` of colors for the left side leaves every right list a spare color, then
`K_{n,nⁿ}` *is* colorable from `L`. This is the extension step used twice inside Kirov–Naimi's
Lemma 8: the right vertices are pairwise non-adjacent, so they may be colored independently. -/
theorem col_pos_of_extends {L : ListAssignment (BV n)} (α : Fin n → ℕ)
    (hα : ∀ i, α i ∈ L (Sum.inl i))
    (h : ∀ φ : Fin n → Fin n, ∃ c ∈ L (Sum.inr φ), c ∉ image α univ) :
    0 < (ERT.K n).col L := by
  choose β hβ hβ' using h
  refine col_pos_iff.mpr ⟨Sum.elim α β, mem_colorings.mpr ⟨?_, ?_⟩⟩
  · rintro (i | φ)
    · exact hα i
    · exact hβ φ
  · rintro (i | φ) (i' | φ') hadj hcon <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hcon
    · simp at hadj
    · exact hβ' φ' (by rw [← hcon]; exact mem_image_of_mem α (mem_univ i))
    · exact hβ' φ (by rw [hcon]; exact mem_image_of_mem α (mem_univ i'))
    · simp at hadj

/-- **Kirov–Naimi 2016, §5, Lemma 8** (first half): if `K_{n,nⁿ}` has *no* coloring from `L` and
every list has at least `n` colors, then the lists on the `n`-element side are pairwise disjoint.

Otherwise two left vertices could be given a common color, leaving at most `n-1` colors used on the
left and so a spare color in every right list. -/
theorem left_disjoint {L : ListAssignment (BV n)} (hcard : ∀ u, n ≤ (L u).card)
    (h0 : (ERT.K n).col L = 0) {i i' : Fin n} (hne : i ≠ i')
    {c : ℕ} (hc : c ∈ L (Sum.inl i)) (hc' : c ∈ L (Sum.inl i')) : False := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnonempty : ∀ a : Fin n, (L (Sum.inl a)).Nonempty :=
    fun a => card_pos.mp (lt_of_lt_of_le hn (hcard _))
  choose γ hγ using hnonempty
  set α : Fin n → ℕ := fun a => if a = i' ∨ a = i then c else γ a with hα_def
  have hαi : α i = c := by simp [hα_def]
  have hαi' : α i' = c := by simp [hα_def]
  have hαmem : ∀ a, α a ∈ L (Sum.inl a) := by
    intro a
    by_cases h : a = i' ∨ a = i
    · rcases h with h | h
      · subst h; rw [hαi']; exact hc'
      · subst h; rw [hαi]; exact hc
    · simpa [hα_def, h] using hγ a
  have himg : image α univ ⊆ image α (univ.erase i') := by
    intro z hz
    rw [mem_image] at hz
    obtain ⟨a, -, rfl⟩ := hz
    by_cases h : a = i'
    · subst h
      exact mem_image.mpr ⟨i, mem_erase.mpr ⟨hne, mem_univ i⟩, by rw [hαi, hαi']⟩
    · exact mem_image.mpr ⟨a, mem_erase.mpr ⟨h, mem_univ a⟩, rfl⟩
  have hcardimg : (image α univ).card < n :=
    calc (image α univ).card ≤ (image α (univ.erase i')).card := card_le_card himg
      _ ≤ (univ.erase i').card := card_image_le
      _ = n - 1 := by rw [card_erase_of_mem (mem_univ i'), card_univ, Fintype.card_fin]
      _ < n := Nat.sub_lt hn one_pos
  have hpos := col_pos_of_extends α hαmem fun φ =>
    exists_mem_notMem_of_card_lt_card (hcardimg.trans_le (hcard (Sum.inr φ)))
  omega

/-- The colors chosen on the left side determine, and are determined by, the *set* of colors they
use — because the left lists are pairwise disjoint (`left_disjoint`). -/
theorem left_image_injOn {L : ListAssignment (BV n)} (hcard : ∀ u, n ≤ (L u).card)
    (h0 : (ERT.K n).col L = 0) :
    Set.InjOn (fun α : Fin n → ℕ => image α univ)
      (Fintype.piFinset fun a : Fin n => L (Sum.inl a)) := by
  intro α hα α' hα' heq
  simp only [Finset.mem_coe, Fintype.mem_piFinset] at hα hα'
  replace heq : image α univ = image α' univ := heq
  funext a
  have : α a ∈ image α' univ := by
    rw [← heq]; exact mem_image_of_mem α (mem_univ a)
  obtain ⟨a', -, ha'⟩ := mem_image.mp this
  by_cases h : a = a'
  · rw [← h] at ha'; exact ha'.symm
  · exact absurd (left_disjoint hcard h0 h (hα a) (ha' ▸ hα' a')) (fun x => x)

/-- Every left choice of colors is *exactly* the list of some right vertex, when `col = 0`. -/
theorem exists_right_eq_image {L : ListAssignment (BV n)} (hcard : ∀ u, n ≤ (L u).card)
    (h0 : (ERT.K n).col L = 0) {α : Fin n → ℕ} (hα : ∀ a, α a ∈ L (Sum.inl a)) :
    ∃ φ : Fin n → Fin n, L (Sum.inr φ) = image α univ := by
  by_contra hcon
  push Not at hcon
  refine absurd (col_pos_of_extends α hα fun φ => ?_) (by omega)
  by_contra h2
  push Not at h2
  refine hcon φ (Finset.eq_of_subset_of_card_le h2 ?_)
  exact le_trans (le_trans card_image_le (by simp)) (hcard (Sum.inr φ))

/-- **Kirov–Naimi 2016, §5, Lemma 8** (second half): if `K_{n,nⁿ}` has no coloring from `L` and
every list has at least `n` colors, then each list on the `n`-element side has *exactly* `n` colors.

The left choices inject into the right lists (distinct choices use distinct color *sets*, by
disjointness, and each such set must be a right list), and there are only `nⁿ` right vertices. -/
theorem left_card_eq (hn : 0 < n) {L : ListAssignment (BV n)} (hcard : ∀ u, n ≤ (L u).card)
    (h0 : (ERT.K n).col L = 0) (i : Fin n) : (L (Sum.inl i)).card = n := by
  have key : ∏ a : Fin n, (L (Sum.inl a)).card ≤ n ^ n := by
    have h1 : (Fintype.piFinset fun a : Fin n => L (Sum.inl a)).card ≤
        (image (fun φ : Fin n → Fin n => L (Sum.inr φ)) univ).card := by
      refine card_le_card_of_injOn _ ?_ (left_image_injOn hcard h0)
      intro α hα
      simp only [Finset.mem_coe, Fintype.mem_piFinset] at hα
      simp only [Finset.mem_coe]
      obtain ⟨φ, hφ⟩ := exists_right_eq_image hcard h0 hα
      exact mem_image.mpr ⟨φ, mem_univ φ, hφ⟩
    rw [Fintype.card_piFinset] at h1
    refine h1.trans ((card_image_le).trans ?_)
    simp
  by_contra hne
  have hlt : n + 1 ≤ (L (Sum.inl i)).card := by have := hcard (Sum.inl i); omega
  have hpow : n ^ n = n * n ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have herase : ∏ _a ∈ univ.erase i, n = n ^ (n - 1) := by
    rw [Finset.prod_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have hge : n ^ (n - 1) ≤ ∏ a ∈ univ.erase i, (L (Sum.inl a)).card := by
    rw [← herase]
    exact Finset.prod_le_prod' fun a _ => hcard (Sum.inl a)
  have hsplit : (L (Sum.inl i)).card * ∏ a ∈ univ.erase i, (L (Sum.inl a)).card =
      ∏ a : Fin n, (L (Sum.inl a)).card :=
    Finset.mul_prod_erase univ (fun a => (L (Sum.inl a)).card) (mem_univ i)
  have hpos : 0 < n ^ (n - 1) := Nat.pow_pos_iff.mpr (Or.inl hn)
  have hchain : n ^ n < n ^ n :=
    calc n ^ n = n * n ^ (n - 1) := hpow
      _ < (n + 1) * n ^ (n - 1) := (Nat.mul_lt_mul_right hpos).mpr (Nat.lt_succ_self n)
      _ ≤ (L (Sum.inl i)).card * ∏ a ∈ univ.erase i, (L (Sum.inl a)).card :=
          Nat.mul_le_mul hlt hge
      _ = ∏ a : Fin n, (L (Sum.inl a)).card := hsplit
      _ ≤ n ^ n := key
  exact absurd hchain (lt_irrefl _)


/-! ### Lemma 9 -/

/-- **Kirov–Naimi 2016, §5, Lemma 9**, in the form Lemma 10 consumes it: for a list assignment on
`K_{n,nⁿ}` all of whose lists have at least `n+1` colors, there is **at most one** color whose
deletion destroys every coloring.

In the paper this is phrased for the complete tripartite `K_{n,nⁿ,1}` with the apex vertex `v`
carrying `[n+1]`: deleting the color of `v` from the lists of its neighbours is exactly the erasure
here, so `col(K_{n,nⁿ,1}, L, v, c) = 0` says `col(K_{n,nⁿ}, L∖c) = 0`.

The hypothesis `2 ≤ n` is **load-bearing**: for `n = 1`, `K_{1,1}` with both lists `{0,1}` has
*two* such colors (see the `#guard`s below), and the whole of §5 collapses at `n = 1`. -/
theorem badColor_unique (hn : 2 ≤ n) {M : ListAssignment (BV n)} (hM : ∀ u, n + 1 ≤ (M u).card)
    {c c' : ℕ} (hc : (ERT.K n).col (fun u => (M u).erase c) = 0)
    (hc' : (ERT.K n).col (fun u => (M u).erase c') = 0) : c = c' := by
  have hn0 : 0 < n := by omega
  have hcard : ∀ (d : ℕ) (u : BV n), n ≤ ((M u).erase d).card := by
    intro d u
    have h1 : (M u).card - 1 ≤ ((M u).erase d).card := Finset.pred_card_le_card_erase
    have h2 := hM u
    omega
  have hmem : ∀ d : ℕ, (ERT.K n).col (fun u => (M u).erase d) = 0 →
      ∀ i : Fin n, d ∈ M (Sum.inl i) := by
    intro d hd i
    by_contra hnot
    have h1 : (M (Sum.inl i)).erase d = M (Sum.inl i) := Finset.erase_eq_of_notMem hnot
    have h2 : ((M (Sum.inl i)).erase d).card = n := left_card_eq hn0 (hcard d) hd i
    rw [h1] at h2
    have := hM (Sum.inl i)
    omega
  by_contra hne
  have hi : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact left_disjoint (hcard c) hc hi
    (Finset.mem_erase.mpr ⟨Ne.symm hne, hmem c' hc' _⟩)
    (Finset.mem_erase.mpr ⟨Ne.symm hne, hmem c' hc' _⟩)

/-! ### The graph `H_{n+1}` -/

/-- The vertices of `H_{n+1}`: the `n` vertices `vᵢ` and `p` vertices `w_k` of a complete bipartite
`K_{n,p}`, together with the vertices of `n²` disjoint copies `G_{i,j}` of `K_{n,nⁿ}`. -/
inductive HV (n p : ℕ)
  /-- the vertex `vᵢ` of the `K_{n,p}` -/
  | v : Fin n → HV n p
  /-- the vertex `w_k` of the `K_{n,p}` -/
  | w : Fin p → HV n p
  /-- a vertex of the copy `G_{i,j}` of `K_{n,nⁿ}` -/
  | g : Fin n → Fin n → BV n → HV n p
  deriving DecidableEq, Fintype

variable (n) (p : ℕ)

/-- Adjacency in `H_{n+1}`: `K_{n,p}` between the `v`s and the `w`s, each `vᵢ` joined to *every*
vertex of the `n` copies `G_{i,1}, …, G_{i,n}`, and each copy internally a `K_{n,nⁿ}`. -/
def HAdj : HV n p → HV n p → Prop
  | .v _, .v _ => False
  | .v _, .w _ => True
  | .v i, .g i' _ _ => i = i'
  | .w _, .v _ => True
  | .w _, .w _ => False
  | .w _, .g _ _ _ => False
  | .g i' _ _, .v i => i' = i
  | .g _ _ _, .w _ => False
  | .g i j u, .g i' j' u' => i = i' ∧ j = j' ∧ (ERT.K n).Adj u u'

instance : DecidableRel (HAdj n p) := by
  intro a b
  cases a <;> cases b <;> simp only [HAdj] <;> infer_instance

/-- **The graph `H_{n+1}` of Kirov–Naimi 2016, §5.** -/
def H : SimpleGraph (HV n p) where
  Adj := HAdj n p
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp only [HAdj] at h ⊢ <;>
      first
        | exact h.symm
        | exact h
        | exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩
  loopless := ⟨by
    intro a h
    cases a <;> simp only [HAdj] at h
    exact (ERT.K n).irrefl h.2.2⟩

instance : DecidableRel (H n p).Adj := inferInstanceAs (DecidableRel (HAdj n p))

variable {n p}

@[simp] lemma H_adj_v_w (i : Fin n) (k : Fin p) : (H n p).Adj (.v i) (.w k) := trivial

@[simp] lemma H_adj_v_g (i : Fin n) (j : Fin n) (u : BV n) : (H n p).Adj (.v i) (.g i j u) := rfl

@[simp] lemma H_adj_g_v (i : Fin n) (j : Fin n) (u : BV n) : (H n p).Adj (.g i j u) (.v i) := rfl

lemma H_adj_g_g {i j : Fin n} {u u' : BV n} (h : (ERT.K n).Adj u u') :
    (H n p).Adj (.g i j u) (.g i j u') := ⟨rfl, rfl, h⟩

@[simp] lemma H_not_adj_v_v (i i' : Fin n) : ¬ (H n p).Adj (.v i) (.v i') := id

@[simp] lemma H_not_adj_w_w (k k' : Fin p) : ¬ (H n p).Adj (.w k) (.w k') := id

@[simp] lemma H_not_adj_w_g (k : Fin p) (i j : Fin n) (u : BV n) :
    ¬ (H n p).Adj (.w k) (.g i j u) := id

@[simp] lemma H_not_adj_g_w (k : Fin p) (i j : Fin n) (u : BV n) :
    ¬ (H n p).Adj (.g i j u) (.w k) := id

/-- A convenient way to check that a coloring of `H_{n+1}` is proper: the only adjacencies are
`vᵢ`-`w_k`, `vᵢ`-`G_{i,j}`, and the internal edges of each copy `G_{i,j}`. -/
lemma isProperColoring_H {f : HV n p → ℕ}
    (hvw : ∀ (i : Fin n) (k : Fin p), f (.v i) ≠ f (.w k))
    (hvg : ∀ (i j : Fin n) (u : BV n), f (.v i) ≠ f (.g i j u))
    (hgg : ∀ i j : Fin n, (ERT.K n).IsProperColoring fun u => f (.g i j u)) :
    (H n p).IsProperColoring f := by
  intro a b hadj
  cases a with
  | v i =>
    cases b with
    | v i' => exact absurd hadj (by simp)
    | w k => exact hvw i k
    | g i' j u => obtain rfl : i = i' := hadj; exact hvg i j u
  | w k =>
    cases b with
    | v i => exact fun hcon => hvw i k hcon.symm
    | w k' => exact absurd hadj (by simp)
    | g _ _ _ => exact absurd hadj (by simp)
  | g i j u =>
    cases b with
    | v i' => obtain rfl : i = i' := hadj; exact fun hcon => hvg i j u hcon.symm
    | w k => exact absurd hadj (by simp)
    | g i' j' u' => obtain ⟨rfl, rfl, h⟩ := hadj; exact hgg i j h


/-! ### The list assignments of Lemma 7 -/

/-- `L_j` of Kirov–Naimi §5: the Erdős–Rubin–Taylor assignment `L₀` on one copy of `K_{n,nⁿ}`, its
colors renamed out of the way (shifted past `2n`, so that they meet neither `[n]` nor the colors
used on the `K_{n,p}` side), together with the extra color `j`. -/
def Lblock (n j : ℕ) : ListAssignment (BV n) :=
  fun u => insert j ((ERT.L₀ n u).image (· + (2 * n + 1)))

/-- The renamed `L₀` — the paper's `L'₀` — still admits no coloring at all. -/
theorem col_shift_L₀ (n : ℕ) :
    (ERT.K n).col (fun u => (ERT.L₀ n u).image (· + (2 * n + 1))) = 0 := by
  rw [col_image_of_injOn (fun a _ b _ h => by omega)]
  exact ERT.col_L₀_eq_zero n

lemma notMem_shift {n j : ℕ} (hj : j < n) (u : BV n) :
    j ∉ (ERT.L₀ n u).image (· + (2 * n + 1)) := by
  intro h
  obtain ⟨x, -, hx⟩ := mem_image.mp h
  omega

/-- Every list of `L_j` has exactly `n+1` colors. -/
theorem Lblock_card {n j : ℕ} (hj : j < n) (u : BV n) : (Lblock n j u).card = n + 1 := by
  have hinj : Function.Injective (· + (2 * n + 1)) := fun a b h => by simpa using h
  rw [Lblock, card_insert_of_notMem (notMem_shift hj u), Finset.card_image_of_injective _ hinj,
    ERT.isNListAssignment_L₀ n u]

/-- The `(n+1)`-list assignment `L` of Kirov–Naimi §5, Lemma 7:
`L(w_k) = {n, …, 2n}`, `L(vᵢ) = [n] ∪ {n+i}`, and `L = L_j` on each copy `G_{i,j}`.
(The paper's colors `1, …, 2n+1` are `0, …, 2n` here.) -/
def LH (n p : ℕ) : ListAssignment (HV n p)
  | .v i => insert (n + i.val) (range n)
  | .w _ => Finset.Ico n (2 * n + 1)
  | .g _ j u => Lblock n j.val u

/-- `L` really is an `(n+1)`-list assignment. -/
theorem isNListAssignment_LH (n p : ℕ) : IsNListAssignment (LH n p) (n + 1) := by
  intro x
  cases x with
  | v i =>
    rw [show LH n p (.v i) = insert (n + i.val) (range n) from rfl,
      card_insert_of_notMem (by simp), card_range]
  | w k =>
    rw [show LH n p (.w k) = Finset.Ico n (2 * n + 1) from rfl, Nat.card_Ico]
    omega
  | g i j u => exact Lblock_card j.isLt u

/-! ### Lemma 7: the colors on the `K_{n,p}` side are forced -/

variable {n p : ℕ}

/-- Every coloring of `H_{n+1}` from `L` gives `vᵢ` the color `n+i`: for each `j`, the copy
`G_{i,j}` must use the color `j` somewhere (otherwise it would be colored from the renamed `L₀`,
which is impossible), and `vᵢ` is adjacent to all of `G_{i,j}`. -/
theorem coloring_v {γ : HV n p → ℕ} (hγ : γ ∈ (H n p).colorings (LH n p)) (i : Fin n) :
    γ (.v i) = n + i.val := by
  obtain ⟨hmem, hproper⟩ := mem_colorings.mp hγ
  have h : γ (.v i) ∈ insert (n + i.val) (range n) := hmem (.v i)
  rcases Finset.mem_insert.mp h with h | h
  · exact h
  · exfalso
    have hj : γ (.v i) < n := mem_range.mp h
    refine col_eq_zero_iff.mp (col_shift_L₀ n) (fun u => γ (.g i ⟨γ (.v i), hj⟩ u)) ?_ ?_
    · intro u
      have hu : γ (.g i ⟨γ (.v i), hj⟩ u) ∈ Lblock n (γ (.v i)) u := hmem (.g i ⟨γ (.v i), hj⟩ u)
      rw [Lblock] at hu
      rcases Finset.mem_insert.mp hu with h2 | h2
      · exact absurd h2 (hproper (H_adj_g_v i ⟨γ (.v i), hj⟩ u))
      · exact h2
    · intro u u' huu' hcon
      exact hproper (H_adj_g_g huu') hcon

/-- Every coloring of `H_{n+1}` from `L` gives every `w_k` the color `2n`: its list is
`{n, …, 2n}`, and the colors `n, …, 2n-1` are taken by its neighbours `v₁, …, vₙ`. -/
theorem coloring_w {γ : HV n p → ℕ} (hγ : γ ∈ (H n p).colorings (LH n p)) (k : Fin p) :
    γ (.w k) = 2 * n := by
  obtain ⟨hmem, hproper⟩ := mem_colorings.mp hγ
  have h : γ (.w k) ∈ Finset.Ico n (2 * n + 1) := hmem (.w k)
  rw [Finset.mem_Ico] at h
  by_contra hne
  have hlt : γ (.w k) - n < n := by omega
  have hv : γ (.v ⟨γ (.w k) - n, hlt⟩) = n + (γ (.w k) - n) := coloring_v hγ _
  exact hproper (H_adj_v_w ⟨γ (.w k) - n, hlt⟩ k) (by omega)

/-- The count of Lemma 7: since the colors of the `vᵢ` and the `w_k` are forced, a coloring of
`H_{n+1}` from `L` is determined by its restrictions to the `n²` copies, and on `G_{i,j}` those
restrictions are exactly the colorings of `K_{n,nⁿ}` from `L_j`. In the paper's notation this is
`col(H_{n+1}, L) = x^{n²}`; only `≤` is needed. -/
theorem col_LH_le (n p : ℕ) :
    (H n p).col (LH n p) ≤ (∏ j : Fin n, (ERT.K n).col (Lblock n j.val)) ^ n := by
  have key : ((H n p).colorings (LH n p)).card ≤
      (Fintype.piFinset fun ij : Fin n × Fin n =>
        (ERT.K n).colorings (Lblock n ij.2.val)).card := by
    refine Finset.card_le_card_of_injOn (fun γ ij u => γ (HV.g ij.1 ij.2 u)) ?_ ?_
    · intro γ hγ
      simp only [Finset.mem_coe, Fintype.mem_piFinset] at hγ ⊢
      intro ij
      obtain ⟨hmem, hproper⟩ := mem_colorings.mp hγ
      exact mem_colorings.mpr ⟨fun u => hmem (.g ij.1 ij.2 u),
        fun u u' huu' hcon => hproper (H_adj_g_g huu') hcon⟩
    · intro γ hγ γ' hγ' heq
      simp only [Finset.mem_coe] at hγ hγ'
      funext x
      cases x with
      | v i => rw [coloring_v hγ i, coloring_v hγ' i]
      | w k => rw [coloring_w hγ k, coloring_w hγ' k]
      | g i j u => exact congrFun (congrFun heq (i, j)) u
  rw [Fintype.card_piFinset] at key
  refine le_trans key (le_of_eq ?_)
  simp only [Fintype.prod_prod_type, col, Finset.prod_const, card_univ, Fintype.card_fin]

/-! ### Lemma 7: the constant list assignment has many colorings -/

/-- The colorings of `H_{n+1}` from `[n+1]` used for the lower bound `col(H_{n+1}, n+1) ≥ nᵖ`:
color the `w_k` arbitrarily from `[n]`, give every `vᵢ` the color `n`, and 2-color each copy
`G_{i,j}` with the colors `0` and `1`. -/
private def stdColoring (n p : ℕ) (ψ : Fin p → Fin n) : HV n p → ℕ
  | .v _ => n
  | .w k => (ψ k).val
  | .g _ _ (Sum.inl _) => 0
  | .g _ _ (Sum.inr _) => 1

/-- `nᵖ ≤ col(H_{n+1}, n+1)`: the `nᵖ` colorings `stdColoring ψ` are distinct. -/
theorem pow_le_colConst (hn : 2 ≤ n) (p : ℕ) : n ^ p ≤ (H n p).colConst (n + 1) := by
  have hcard : (univ : Finset (Fin p → Fin n)).card = n ^ p := by simp
  rw [← hcard]
  show _ ≤ ((H n p).colorings (constList (HV n p) (n + 1))).card
  refine Finset.card_le_card_of_injOn (stdColoring n p) ?_ ?_
  · intro ψ _
    simp only [Finset.mem_coe]
    refine mem_colorings.mpr ⟨?_, ?_⟩
    · intro x
      rw [constList_apply, mem_range]
      cases x with
      | v i => simp only [stdColoring]; omega
      | w k => simp only [stdColoring]; have := (ψ k).isLt; omega
      | g i j u =>
        cases u with
        | inl a => simp only [stdColoring]; omega
        | inr φ => simp only [stdColoring]; omega
    · refine isProperColoring_H (fun i k => ?_) (fun i j u => ?_) (fun i j => ?_)
      · simp only [stdColoring]
        have := (ψ k).isLt
        omega
      · cases u with
        | inl a => simp only [stdColoring]; omega
        | inr φ => simp only [stdColoring]; omega
      · intro u u' huu' hcon
        cases u with
        | inl a =>
          cases u' with
          | inl a' => exact absurd huu' (by simp)
          | inr φ' => simp only [stdColoring] at hcon; omega
        | inr φ =>
          cases u' with
          | inl a' => simp only [stdColoring] at hcon; omega
          | inr φ' => exact absurd huu' (by simp)
  · intro ψ _ ψ' _ heq
    funext k
    exact Fin.val_injective (congrFun heq (HV.w k))

/-! ### Lemma 7 -/

/-- **Kirov–Naimi 2016, §5, Lemma 7**: `H_{n+1}` is not enumeratively chromatic-choosable at `n+1`
(the paper's "not `(n+1)`-monophilic"), whenever the number `p` of `w`-vertices is large enough that
`nᵖ` exceeds the number of colorings from `L`.

The hypothesis `2 ≤ n` is load-bearing on both sides: see the module docstring. -/
theorem not_ecc (hn : 2 ≤ n) {p : ℕ}
    (hp : (∏ j : Fin n, (ERT.K n).col (Lblock n j.val)) ^ n < n ^ p) :
    ¬ (H n p).ECCAt (n + 1) := by
  intro hecc
  have h1 := hecc (LH n p) (isNListAssignment_LH n p)
  have h2 := col_LH_le n p
  have h3 := pow_le_colConst hn p
  omega

/-- Such a `p` exists: `p = x^{n²}` will do, since `m < nᵐ` for `n ≥ 2`. -/
theorem exists_pow_lt (hn : 2 ≤ n) :
    ∃ p : ℕ, (∏ j : Fin n, (ERT.K n).col (Lblock n j.val)) ^ n < n ^ p :=
  ⟨(∏ j : Fin n, (ERT.K n).col (Lblock n j.val)) ^ n, Nat.lt_pow_self (by omega)⟩


/-! ### Lemma 10 -/

/-- The coloring of `H_{n+1}` assembled in Lemma 10 out of a color for each `vᵢ`, a color for each
`w_k`, and a coloring of each copy `G_{i,j}`. -/
private def assemble (n p : ℕ) (c : Fin n → ℕ) (d : Fin p → ℕ) (f : Fin n → Fin n → BV n → ℕ) :
    HV n p → ℕ
  | .v i => c i
  | .w k => d k
  | .g i j u => f i j u

/-- **Kirov–Naimi 2016, §5, Lemma 10**: `H_{n+1}` is `(n+1)`-choosable.

By Lemma 9 (`badColor_unique`) at most one color of `L(vᵢ)` kills the copy `G_{i,j}`, for each of
the `n` values of `j`; as `|L(vᵢ)| = n+1` some color `cᵢ` is safe for all `j` at once. Each `w_k`
has only `n` neighbours, so its list also has a color to spare.

Again `2 ≤ n` is load-bearing, through Lemma 9. -/
theorem choosable (hn : 2 ≤ n) (p : ℕ) : (H n p).Choosable (n + 1) := by
  classical
  intro L hL
  -- Step 1: for each `i`, a color of `L(vᵢ)` that no copy `G_{i,j}` objects to.
  have hgood : ∀ i : Fin n, ∃ c ∈ L (.v i),
      ∀ j : Fin n, 0 < (ERT.K n).col fun u => (L (HV.g i j u)).erase c := by
    intro i
    set bad : Finset ℕ := (univ : Finset (Fin n)).biUnion fun j =>
      (L (HV.v i)).filter fun c => (ERT.K n).col (fun u => (L (HV.g i j u)).erase c) = 0 with hbad
    have hbadsub : bad ⊆ L (.v i) := by
      intro z hz
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_filter.mp hj).1
    have hbadcard : bad.card ≤ n := by
      refine le_trans Finset.card_biUnion_le ?_
      have hone : ∀ j : Fin n, ((L (HV.v i)).filter fun z =>
          (ERT.K n).col (fun u => (L (HV.g i j u)).erase z) = 0).card ≤ 1 := by
        intro j
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        exact badColor_unique hn (fun u => le_of_eq (hL (HV.g i j u)).symm)
          (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      calc ∑ j : Fin n, ((L (HV.v i)).filter fun z =>
              (ERT.K n).col (fun u => (L (HV.g i j u)).erase z) = 0).card
          ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => hone j
        _ = n := by simp
    have hpos : 0 < (L (.v i) \ bad).card := by
      rw [Finset.card_sdiff_of_subset hbadsub, hL (.v i)]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_sdiff] at hz
    refine ⟨z, hz.1, fun j => ?_⟩
    rcases Nat.eq_zero_or_pos ((ERT.K n).col fun u => (L (HV.g i j u)).erase z) with h | h
    · exact absurd (Finset.mem_biUnion.mpr ⟨j, mem_univ j, Finset.mem_filter.mpr ⟨hz.1, h⟩⟩) hz.2
    · exact h
  choose c hc hcgood using hgood
  -- Step 2: a coloring of each copy avoiding the color of its `vᵢ`.
  have hblock : ∀ i j : Fin n,
      ∃ f, f ∈ (ERT.K n).colorings fun u => (L (HV.g i j u)).erase (c i) :=
    fun i j => col_pos_iff.mp (hcgood i j)
  choose f hf using hblock
  -- Step 3: each `w_k` has only the `n` neighbours `v₁, …, vₙ`.
  have hw : ∀ k : Fin p, ∃ z ∈ L (.w k), z ∉ image c univ := by
    intro k
    refine exists_mem_notMem_of_card_lt_card ?_
    calc (image c univ).card ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by simp
      _ < n + 1 := Nat.lt_succ_self n
      _ = (L (.w k)).card := (hL (.w k)).symm
  choose d hd hd' using hw
  refine col_pos_iff.mpr ⟨assemble n p c d f, mem_colorings.mpr ⟨?_, ?_⟩⟩
  · intro x
    cases x with
    | v i => exact hc i
    | w k => exact hd k
    | g i j u =>
      exact Finset.mem_of_mem_erase ((mem_colorings.mp (hf i j)).1 u)
  · refine isProperColoring_H (fun i k => ?_) (fun i j u => ?_) (fun i j => ?_)
    · show c i ≠ d k
      intro hcon
      exact hd' k (hcon ▸ mem_image_of_mem c (mem_univ i))
    · show c i ≠ f i j u
      exact fun hcon =>
        (Finset.ne_of_mem_erase ((mem_colorings.mp (hf i j)).1 u)) hcon.symm
    · exact (mem_colorings.mp (hf i j)).2

/-! ### The theorem of §5 -/

/-- **Kirov–Naimi 2016, §5** (Lemmas 7–10): for every `n ≥ 2` there is a graph — the paper's
`H_{n+1}` — that is `(n+1)`-choosable but **not** enumeratively chromatic-choosable at `n+1`
(not "`(n+1)`-monophilic"). Choosability and enumerative chromatic-choosability are therefore
different properties.

See the module docstring for why `n = 1` is excluded, and what stands in for it. -/
theorem exists_choosable_not_ecc (hn : 2 ≤ n) :
    ∃ p : ℕ, (H n p).Choosable (n + 1) ∧ ¬ (H n p).ECCAt (n + 1) := by
  obtain ⟨p, hp⟩ := exists_pow_lt hn
  exact ⟨p, choosable hn p, not_ecc hn hp⟩

/-! ### List size `2`, where `H_{n+1}` does not reach -/

/-- **Kirov–Naimi 2016, §5, at every list size**: for every `k ≥ 2` there is a graph that is
`k`-choosable but *not* enumeratively chromatic-choosable at `k` (the paper's "`k`-choosable but not
`k`-monophilic"). For `k ≥ 3` the witness is the paper's `H_k`; for `k = 2` it is `θ_{2,2,4}`,
because `H₂` does not exist — see the module docstring. -/
theorem exists_choosable_not_ecc_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ (V : Type) (iF : Fintype V) (iD : DecidableEq V) (G : SimpleGraph V)
      (iA : DecidableRel G.Adj), @Choosable V iF iD G iA k ∧ ¬ @ECCAt V iF iD G iA k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  cases m with
  | zero =>
      exact ⟨ListColoring.ThetaV 2, inferInstance, inferInstance, ListColoring.theta 2,
        inferInstance, ListColoring.choosable_and_not_ecc_theta 2 (by omega)⟩
  | succ m =>
      obtain ⟨p, hch, hne⟩ := exists_choosable_not_ecc (n := m + 2) (by omega)
      exact ⟨HV (m + 2) p, inferInstance, inferInstance, H (m + 2) p, inferInstance, hch, hne⟩

/-! ### Numerical checks

Kernel evaluation reaches `K_{2,4}` and the whole of `H₂` (the `n = 1` graph), which is what the
checks below use; `H₃` has `52` vertices and `3⁵²` candidate colorings, far out of reach, and was
checked externally instead (see the module docstring). -/

-- `x = col(K_{2,4}, L_j) = 80`, independent of `j`, as the paper asserts.
#guard (ERT.K 2).col (Lblock 2 0) = 80
#guard (ERT.K 2).col (Lblock 2 1) = 80
#guard ∀ u, (Lblock 2 0 u).card = 3
#guard ∀ u, (Lblock 2 1 u).card = 3

-- Lemma 9 for `K_{2,4}`, in the danger zone: `L_0` really has a bad color, and only one.
#guard ((range 9).filter fun z => (ERT.K 2).col (fun u => (Lblock 2 0 u).erase z) = 0) = {0}
#guard ((range 9).filter fun z => (ERT.K 2).col (fun u => (Lblock 2 1 u).erase z) = 0) = {1}

-- **Lemma 9 fails at `n = 1`**: `K_{1,1}` with both lists `{0,1}` — a `2`-list assignment — has
-- *two* colors whose deletion destroys every coloring.
#guard (ERT.K 1).col (fun _ => ({0, 1} : Finset ℕ).erase 0) = 0
#guard (ERT.K 1).col (fun _ => ({0, 1} : Finset ℕ).erase 1) = 0

-- **Lemma 7 fails at `n = 1`**: `H₂` contains a triangle, so `col(H₂, 2) = 0 < 2 = col(H₂, L)` —
-- the inequality the lemma claims runs the *other* way, and `H₂` is (vacuously) `2`-monophilic.
#guard (H 1 1).colConst 2 = 0
#guard (H 1 1).col (LH 1 1) = 2

-- The counting of Lemma 7 (`col_LH_le`) is an equality at `n = 1`, where it can be evaluated:
-- `col(H₂, L) = x¹ = 2`.
#guard (ERT.K 1).col (Lblock 1 0) = 2
#guard (H 1 1).col (LH 1 1) = (∏ j : Fin 1, (ERT.K 1).col (Lblock 1 j.val)) ^ 1

-- The forced colors of Lemma 7: `γ(vᵢ) = n+i` and `γ(w_k) = 2n`, checked on `H₂`.
#guard ∀ γ ∈ (H 1 1).colorings (LH 1 1), γ (.v 0) = 1 ∧ γ (.w 0) = 2

-- `L` is an `(n+1)`-list assignment, and the lower-bound coloring of Lemma 7 is proper.
--
-- The second check is `stdColoring … ∈ (H 2 3).colorings (constList (HV 2 3) 3)` split into its two
-- conjuncts. Membership in `colorings` goes through `Finset.decidableMem`, which materializes and
-- scans `Fintype.piFinset` — `3^29` functions here, which exhausts memory rather than failing.
-- The conjuncts are the same statement and cost `|V|²`.
#guard ∀ x, ((LH 2 3) x).card = 3
#guard ∀ x, stdColoring 2 3 (fun k => if k = 0 then 0 else 1) x ∈ constList (HV 2 3) 3 x
#guard (H 2 3).IsProperColoring (stdColoring 2 3 (fun k => if k = 0 then 0 else 1))

end KN5
end SimpleGraph

#print axioms SimpleGraph.KN5.left_disjoint
#print axioms SimpleGraph.KN5.left_card_eq
#print axioms SimpleGraph.KN5.badColor_unique
#print axioms SimpleGraph.KN5.not_ecc
#print axioms SimpleGraph.KN5.choosable
#print axioms SimpleGraph.KN5.exists_choosable_not_ecc
#print axioms SimpleGraph.KN5.exists_choosable_not_ecc_of_two_le
