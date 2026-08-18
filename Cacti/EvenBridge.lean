/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
/-
The graph → tensor bridge for even cycles: conditioning on one bipartition class.
-/
import Cacti.Tensor
import Cacti.Induction
import Cacti.PathCone

namespace ListColoring

open Finset SimpleGraph

section EvenBridge

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The index type of an even cycle `C_{2(M+1)}`, split into its two bipartition classes:
`inl i` is the `i`-th **terminal**, `inr i` the **internal** vertex between terminals `i` and
`i+1`. -/
abbrev CycIx (M : ℕ) := Fin (M + 1) ⊕ Fin (M + 1)

/-- Even-cycle adjacency in terminal/internal coordinates: internal `i` is joined to terminals
`i` and `i+1`, and there are no other edges. -/
def CycAdj {M : ℕ} : CycIx M → CycIx M → Prop
  | Sum.inl i, Sum.inr j => i = j ∨ i = j + 1
  | Sum.inr i, Sum.inl j => j = i ∨ j = i + 1
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

variable {M : ℕ}

/-- The `i`-th terminal vertex. -/
def tv (jx : CycIx M ≃ V) (i : Fin (M + 1)) : V := jx (Sum.inl i)

/-- The `i`-th internal vertex. -/
def iv (jx : CycIx M ≃ V) (i : Fin (M + 1)) : V := jx (Sum.inr i)

/-- Assembling a colouring from a terminal word `a` and an internal word `b`. -/
def glue (jx : CycIx M ≃ V) (a b : Fin (M + 1) → ℕ) : V → ℕ := fun v => Sum.elim a b (jx.symm v)

@[simp] theorem glue_tv (jx : CycIx M ≃ V) (a b : Fin (M + 1) → ℕ) (i : Fin (M + 1)) :
    glue jx a b (tv jx i) = a i := by
  simp [glue, tv]

@[simp] theorem glue_iv (jx : CycIx M ≃ V) (a b : Fin (M + 1) → ℕ) (i : Fin (M + 1)) :
    glue jx a b (iv jx i) = b i := by
  simp [glue, iv]

theorem glue_restrict (jx : CycIx M ≃ V) (f : V → ℕ) :
    glue jx (fun i => f (tv jx i)) (fun i => f (iv jx i)) = f := by
  funext v
  obtain ⟨x, rfl⟩ := jx.surjective v
  cases x <;> simp [glue, tv, iv]

/-- The **terminal words**: one colour from each terminal list. -/
def wordSet (jx : CycIx M ≃ V) (L : ListAssignment V) : Finset (Fin (M + 1) → ℕ) :=
  Fintype.piFinset (fun i => L (tv jx i))

/-- The **internal completions** of a terminal word: at each internal vertex, a colour of its
list avoiding the colours of its two terminal neighbours. -/
def innerSet (jx : CycIx M ≃ V) (L : ListAssignment V) (a : Fin (M + 1) → ℕ) :
    Finset (Fin (M + 1) → ℕ) :=
  Fintype.piFinset (fun i => ((L (iv jx i)).erase (a i)).erase (a (i + 1)))

theorem mem_wordSet {jx : CycIx M ≃ V} {L : ListAssignment V} {a : Fin (M + 1) → ℕ} :
    a ∈ wordSet jx L ↔ ∀ i, a i ∈ L (tv jx i) := by
  simp [wordSet, Fintype.mem_piFinset]

theorem mem_innerSet {jx : CycIx M ≃ V} {L : ListAssignment V} {a b : Fin (M + 1) → ℕ} :
    b ∈ innerSet jx L a ↔ ∀ i, b i ∈ L (iv jx i) ∧ b i ≠ a i ∧ b i ≠ a (i + 1) := by
  simp only [innerSet, Fintype.mem_piFinset, Finset.mem_erase]
  constructor
  · intro h i
    exact ⟨(h i).2.2, (h i).2.1, (h i).1⟩
  · intro h i
    exact ⟨(h i).2.2, (h i).2.1, (h i).1⟩

/-- **The easy half of the bridge**: every terminal word with an internal completion assembles
into a proper `L`-colouring of the cycle. -/
theorem glue_mem_colorings (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) {a b : Fin (M + 1) → ℕ} (ha : a ∈ wordSet jx L)
    (hb : b ∈ innerSet jx L a) : glue jx a b ∈ G.colorings L := by
  rw [mem_wordSet] at ha
  rw [mem_innerSet] at hb
  rw [SimpleGraph.mem_colorings_iff]
  refine ⟨fun v => ?_, fun u v huv => ?_⟩
  · obtain ⟨x, rfl⟩ := jx.surjective v
    cases x with
    | inl i => exact (glue_tv jx a b i) ▸ ha i
    | inr i => exact (glue_iv jx a b i) ▸ (hb i).1
  · obtain ⟨x, rfl⟩ := jx.surjective u
    obtain ⟨y, rfl⟩ := jx.surjective v
    have h := (hadj x y).mp huv
    cases x with
    | inl i =>
      cases y with
      | inl j => exact absurd h (by simp [CycAdj])
      | inr j =>
        rw [show jx (Sum.inl i) = tv jx i from rfl, show jx (Sum.inr j) = iv jx j from rfl,
          glue_tv, glue_iv]
        rcases (show i = j ∨ i = j + 1 from h) with hij | hij
        · rw [hij]; exact fun hc => (hb j).2.1 hc.symm
        · rw [hij]; exact fun hc => (hb j).2.2 hc.symm
    | inr i =>
      cases y with
      | inl j =>
        rw [show jx (Sum.inr i) = iv jx i from rfl, show jx (Sum.inl j) = tv jx j from rfl,
          glue_iv, glue_tv]
        rcases (show j = i ∨ j = i + 1 from h) with hij | hij
        · rw [hij]; exact (hb i).2.1
        · rw [hij]; exact (hb i).2.2
      | inr j => exact absurd h (by simp [CycAdj])

/-- **The hard half of the bridge**: every proper `L`-colouring restricts to a terminal word
with an internal completion. -/
theorem restrict_mem (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) {f : V → ℕ} (hf : f ∈ G.colorings L) :
    (fun i => f (tv jx i)) ∈ wordSet jx L ∧
      (fun i => f (iv jx i)) ∈ innerSet jx L (fun i => f (tv jx i)) := by
  rw [SimpleGraph.mem_colorings_iff] at hf
  obtain ⟨hmem, hprop⟩ := hf
  refine ⟨mem_wordSet.mpr fun i => hmem _, mem_innerSet.mpr fun i => ⟨hmem _, ?_, ?_⟩⟩
  · exact hprop _ _ ((hadj (Sum.inr i) (Sum.inl i)).mpr (Or.inl rfl))
  · exact hprop _ _ ((hadj (Sum.inr i) (Sum.inl (i + 1))).mpr (Or.inr rfl))

/-- **The bridge as a reindexing of sums**: summing any quantity over the proper `L`-colourings
of an even cycle is summing it over terminal words together with their internal completions.
A predicate `Q` on the terminal word may be carried along (it is `a 0 = c` for the rooted
count). -/
theorem sum_colorings_eq_sum_sigma (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (F : (V → ℕ) → ℕ)
    (Q : (Fin (M + 1) → ℕ) → Prop) [DecidablePred Q] :
    ∑ f ∈ (G.colorings L).filter (fun f => Q (fun i => f (tv jx i))), F f
      = ∑ p ∈ ((wordSet jx L).filter Q).sigma (innerSet jx L), F (glue jx p.1 p.2) := by
  classical
  refine Finset.sum_nbij' (i := fun f => ⟨fun i => f (tv jx i), fun i => f (iv jx i)⟩)
    (j := fun p => glue jx p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨h1, h2⟩ := restrict_mem jx hadj L hf.1
    exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨h1, hf.2⟩, h2⟩
  · intro p hp
    rw [Finset.mem_sigma, Finset.mem_filter] at hp
    obtain ⟨⟨ha, hQ⟩, hb⟩ := hp
    refine Finset.mem_filter.mpr ⟨glue_mem_colorings jx hadj L ha hb, ?_⟩
    simpa using hQ
  · intro f _
    exact glue_restrict jx f
  · intro p _
    ext <;> simp
  · intro f _
    rw [glue_restrict]

/-- **The graph → tensor bridge for even cycles** (the analogue of `exists_cover_model` on the
even side): the weighted count of an even cycle is the sum, over terminal words, of the product
of the terminal weights times the two-edge path sums `pathN` at the internal vertices. -/
theorem wcol_eq_sum_words (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (w : V → ℕ → ℕ) :
    wcol G L w = ∑ a ∈ wordSet jx L,
      (∏ i, w (tv jx i) (a i)) *
        ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (a i) (a (i + 1)) := by
  classical
  have hfilter : (G.colorings L).filter (fun _ => True) = G.colorings L :=
    Finset.filter_true_of_mem (fun _ _ => trivial)
  have hwfilter : (wordSet jx L).filter (fun _ => True) = wordSet jx L :=
    Finset.filter_true_of_mem (fun _ _ => trivial)
  rw [wcol, ← hfilter,
    sum_colorings_eq_sum_sigma jx hadj L (fun f => ∏ v, w v (f v)) (fun _ => True), hwfilter,
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hsplit : ∀ b : Fin (M + 1) → ℕ, (∏ v, w v (glue jx a b v))
      = (∏ i, w (tv jx i) (a i)) * ∏ i, w (iv jx i) (b i) := by
    intro b
    rw [← Equiv.prod_comp jx (fun v => w v (glue jx a b v)), Fintype.prod_sum_type]
    congr 1 <;> exact Finset.prod_congr rfl fun i _ => by simp [glue, tv, iv]
  rw [Finset.sum_congr rfl (fun b _ => hsplit b), ← Finset.mul_sum]
  congr 1
  rw [innerSet, ← Finset.prod_univ_sum]
  rfl

/-- The rooted form of the bridge: the rooted weighted count at terminal `0` is the sum of the
same word weights over the terminal words taking the value `c` at position `0`. -/
theorem rootedWcol_eq_sum_words (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (c : ℕ) :
    rootedWcol G L w (tv jx 0) c = ∑ a ∈ (wordSet jx L).filter (fun a => a 0 = c),
      (∏ i, w (tv jx i) (a i)) *
        ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (a i) (a (i + 1)) := by
  classical
  rw [rootedWcol,
    sum_colorings_eq_sum_sigma jx hadj L (fun f => ∏ v, w v (f v)) (fun a => a 0 = c),
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hsplit : ∀ b : Fin (M + 1) → ℕ, (∏ v, w v (glue jx a b v))
      = (∏ i, w (tv jx i) (a i)) * ∏ i, w (iv jx i) (b i) := by
    intro b
    rw [← Equiv.prod_comp jx (fun v => w v (glue jx a b v)), Fintype.prod_sum_type]
    congr 1 <;> exact Finset.prod_congr rfl fun i _ => by simp [glue, tv, iv]
  rw [Finset.sum_congr rfl (fun b _ => hsplit b), ← Finset.mul_sum]
  congr 1
  rw [innerSet, ← Finset.prod_univ_sum]
  rfl

end EvenBridge

section Reindex

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The interleaving index: terminal `i` sits at cycle position `2i`, internal `i` at `2i+1`. -/
def cycIdx (M : ℕ) : CycIx M → Fin (2 * M + 1 + 1)
  | Sum.inl i => ⟨2 * i.val, by have := i.isLt; omega⟩
  | Sum.inr i => ⟨2 * i.val + 1, by have := i.isLt; omega⟩

/-- Its inverse: even positions are terminals, odd positions internal. -/
def cycUnidx (M : ℕ) (k : Fin (2 * M + 1 + 1)) : CycIx M :=
  if k.val % 2 = 0 then Sum.inl ⟨k.val / 2, by have := k.isLt; omega⟩
  else Sum.inr ⟨k.val / 2, by have := k.isLt; omega⟩

/-- The even cycle's positions, split into its two bipartition classes. -/
def cycEquiv (M : ℕ) : CycIx M ≃ Fin (2 * M + 1 + 1) where
  toFun := cycIdx M
  invFun := cycUnidx M
  left_inv := by
    intro x
    cases x with
    | inl i =>
      show cycUnidx M ⟨2 * i.val, _⟩ = _
      rw [cycUnidx, if_pos (by show 2 * i.val % 2 = 0; omega)]
      exact congrArg Sum.inl (Fin.ext (by show 2 * i.val / 2 = i.val; omega))
    | inr i =>
      show cycUnidx M ⟨2 * i.val + 1, _⟩ = _
      rw [cycUnidx, if_neg (by show ¬ (2 * i.val + 1) % 2 = 0; omega)]
      exact congrArg Sum.inr (Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega))
  right_inv := by
    intro k
    rw [cycUnidx]
    by_cases hk : k.val % 2 = 0
    · rw [if_pos hk]
      exact Fin.ext (by show 2 * (k.val / 2) = k.val; omega)
    · rw [if_neg hk]
      exact Fin.ext (by show 2 * (k.val / 2) + 1 = k.val; omega)

theorem fin_add_one_val {n : ℕ} (a : Fin (n + 1)) : (a + 1).val = (a.val + 1) % (n + 1) := by
  rw [Fin.add_def]
  simp [Nat.add_mod_mod]

/-- The successor modulo a bound, as a decidable case split. -/
theorem succ_mod_of_lt (a n : ℕ) (h : a < n) : (a + 1) % n = if a + 1 = n then 0 else a + 1 := by
  by_cases he : a + 1 = n
  · rw [if_pos he, he, Nat.mod_self]
  · rw [if_neg he, Nat.mod_eq_of_lt (by omega)]

/-- **The adjacency dictionary**: cyclic adjacency of the `2M+2` positions of an even cycle is
exactly `CycAdj` in terminal/internal coordinates. -/
theorem cycIdx_adj (M : ℕ) (x y : CycIx M) :
    (cycIdx M y = cycIdx M x + 1 ∨ cycIdx M x = cycIdx M y + 1) ↔ CycAdj x y := by
  cases x with
  | inl i =>
    have hi := i.isLt
    cases y with
    | inl j =>
      have hj := j.isLt
      simp only [CycAdj, Fin.ext_iff, fin_add_one_val, cycIdx, iff_false]
      rw [succ_mod_of_lt (2 * i.val) (2 * M + 1 + 1) (by omega),
        succ_mod_of_lt (2 * j.val) (2 * M + 1 + 1) (by omega)]
      split_ifs <;> omega
    | inr j =>
      have hj := j.isLt
      simp only [CycAdj, Fin.ext_iff, fin_add_one_val, cycIdx]
      rw [succ_mod_of_lt (2 * i.val) (2 * M + 1 + 1) (by omega),
        succ_mod_of_lt (2 * j.val + 1) (2 * M + 1 + 1) (by omega),
        succ_mod_of_lt j.val (M + 1) (by omega)]
      split_ifs <;> omega
  | inr i =>
    have hi := i.isLt
    cases y with
    | inl j =>
      have hj := j.isLt
      simp only [CycAdj, Fin.ext_iff, fin_add_one_val, cycIdx]
      rw [succ_mod_of_lt (2 * i.val + 1) (2 * M + 1 + 1) (by omega),
        succ_mod_of_lt (2 * j.val) (2 * M + 1 + 1) (by omega),
        succ_mod_of_lt i.val (M + 1) (by omega)]
      split_ifs <;> omega
    | inr j =>
      have hj := j.isLt
      simp only [CycAdj, Fin.ext_iff, fin_add_one_val, cycIdx, iff_false]
      rw [succ_mod_of_lt (2 * i.val + 1) (2 * M + 1 + 1) (by omega),
        succ_mod_of_lt (2 * j.val + 1) (2 * M + 1 + 1) (by omega)]
      split_ifs <;> (try simp only [false_or, or_false]) <;> (try exact not_false) <;> omega

/-- **The even cycle in terminal/internal coordinates**: a cyclically indexed graph on an even
number of vertices carries the terminal/internal model, with the same root. -/
theorem exists_cyc_model {M : ℕ} (ix : Fin (2 * M + 1 + 1) ≃ V)
    (hadj : ∀ i j : Fin (2 * M + 1 + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) :
    ∃ jx : CycIx M ≃ V, (∀ x y, G.Adj (jx x) (jx y) ↔ CycAdj x y) ∧ tv jx 0 = ix 0 := by
  refine ⟨(cycEquiv M).trans ix, fun x y => ?_, ?_⟩
  · rw [show ((cycEquiv M).trans ix) x = ix (cycIdx M x) from rfl,
      show ((cycEquiv M).trans ix) y = ix (cycIdx M y) from rfl, hadj]
    exact cycIdx_adj M x y
  · show ix (cycIdx M (Sum.inl 0)) = ix 0
    congr 1

/-- **The bridge in the coordinates of `cycle_gm_bound_even`**: an even cycle indexed by
`Fin (m+1)` with the repo's cyclic adjacency hypothesis carries a terminal/internal model with
the same root `ix 0`, in which the rooted weighted count is the word sum of the tensor model.
`M + 1` is the number of terminals, i.e. the handoff's `m` for `C_{2m}`. -/
theorem exists_even_cycle_word_model {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Even (m + 1)) (L : ListAssignment V) (w : V → ℕ → ℕ) :
    ∃ (M : ℕ) (jx : CycIx M ≃ V), 1 ≤ M ∧ tv jx 0 = ix 0 ∧
      (∀ x y, G.Adj (jx x) (jx y) ↔ CycAdj x y) ∧
      ∀ c, rootedWcol G L w (ix 0) c
        = ∑ a ∈ (wordSet jx L).filter (fun a => a 0 = c),
            (∏ i, w (tv jx i) (a i)) *
              ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (a i) (a (i + 1)) := by
  obtain ⟨r, hr⟩ := hpar
  obtain ⟨M, rfl⟩ : ∃ M, m = 2 * M + 1 := ⟨r - 1, by omega⟩
  obtain ⟨jx, hjx, hroot⟩ := exists_cyc_model ix hadj
  refine ⟨M, jx, by omega, hroot, hjx, fun c => ?_⟩
  rw [← hroot]
  exact rootedWcol_eq_sum_words jx hjx L w c

/-- **The capacity form consumed by the weighted AM–GM step**: any family of terminal words
taking the root colour `c` contributes at most the rooted weighted count.  This is the direction
§5.6 uses, and it needs no completeness of the family. -/
theorem sum_words_le_rootedWcol {M : ℕ} (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (c : ℕ) (S : Finset (Fin (M + 1) → ℕ))
    (hS : S ⊆ (wordSet jx L).filter (fun a => a 0 = c)) :
    ∑ a ∈ S, (∏ i, w (tv jx i) (a i)) *
        ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (a i) (a (i + 1))
      ≤ rootedWcol G L w (tv jx 0) c := by
  rw [rootedWcol_eq_sum_words jx hadj L w c]
  exact Finset.sum_le_sum_of_subset hS

end Reindex

section TensorCoords

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The equality-extending enumeration chain of the terminal lists** (the §5.2 relabelling
data, on the terminal cycle rather than on all of `C_{2m}`): `exists_enum_chain` applied to the
terminals.  Together with a closing permutation this is what turns terminal words into index
words with a single holonomy at the seam. -/
theorem exists_terminal_enum_chain {M k : ℕ} (jx : CycIx M ≃ V) (L : ListAssignment V)
    (hL : IsNListAssignment L k) :
    ∃ σ : Fin (M + 1) → Fin k → ℕ,
      (∀ i x, σ i x ∈ L (tv jx i)) ∧ (∀ i, Function.Injective (σ i)) ∧
      ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin k),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x :=
  exists_enum_chain (by omega) (fun i => L (tv jx i)) (fun i => hL (tv jx i))

/-- **Terminal words in tensor coordinates**: an enumeration of each terminal list turns the sum
over terminal words into a sum over index words `g : Fin (M+1) → Fin k`, which is the index set
of the reference tensor of §5.2. -/
theorem sum_index_eq_sum_wordSet {M k : ℕ} (jx : CycIx M ≃ V) (L : ListAssignment V)
    (hL : IsNListAssignment L k) (σ : Fin (M + 1) → Fin k → ℕ)
    (hσmem : ∀ i x, σ i x ∈ L (tv jx i)) (hσinj : ∀ i, Function.Injective (σ i))
    (F : (Fin (M + 1) → ℕ) → ℕ) (Q : (Fin (M + 1) → ℕ) → Prop) [DecidablePred Q] :
    ∑ g ∈ (Finset.univ : Finset (Fin (M + 1) → Fin k)).filter
        (fun g => Q (fun i => σ i (g i))), F (fun i => σ i (g i))
      = ∑ a ∈ (wordSet jx L).filter Q, F a := by
  classical
  refine Finset.sum_nbij (i := fun g => (fun i => σ i (g i))) ?_ ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨mem_wordSet.mpr fun i => hσmem i (g i), hg.2⟩
  · intro g₁ _ g₂ _ h
    funext i
    exact hσinj i (congrFun h i)
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter, mem_wordSet] at ha
    choose g hg using fun i => enum_surj (hL (tv jx i)) (hσmem i) (hσinj i) (ha.1 i)
    have hga : (fun i => σ i (g i)) = a := funext hg
    exact ⟨g, by rw [Finset.mem_coe, Finset.mem_filter]
                 exact ⟨Finset.mem_univ _, by rw [hga]; exact ha.2⟩, hga⟩
  · intro g _
    rfl

/-- **The bridge in tensor coordinates**: the rooted weighted count of an even cycle at the root
colour `σ 0 c` is a sum over index words `g : Fin (M+1) → Fin k` with `g 0 = c`, of the terminal
weights times the two-edge path sums.  This is the exact input of the §5.2–§5.6 tensor argument:
the summand is `X(g)`, the reference tensor `U` weights these same index words. -/
theorem rootedWcol_eq_sum_index {M k : ℕ} (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (hL : IsNListAssignment L k) (w : V → ℕ → ℕ)
    (σ : Fin (M + 1) → Fin k → ℕ)
    (hσmem : ∀ i x, σ i x ∈ L (tv jx i)) (hσinj : ∀ i, Function.Injective (σ i)) (c : Fin k) :
    rootedWcol G L w (tv jx 0) (σ 0 c)
      = ∑ g ∈ (Finset.univ : Finset (Fin (M + 1) → Fin k)).filter (fun g => g 0 = c),
          (∏ i, w (tv jx i) (σ i (g i))) *
            ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))) := by
  classical
  rw [rootedWcol_eq_sum_words jx hadj L w (σ 0 c),
    ← sum_index_eq_sum_wordSet jx L hL σ hσmem hσinj
      (fun a => (∏ i, w (tv jx i) (a i)) *
        ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (a i) (a (i + 1)))
      (fun a => a 0 = σ 0 c)]
  refine Finset.sum_congr ?_ (fun g _ => rfl)
  refine Finset.filter_congr fun g _ => ?_
  exact ⟨fun h => hσinj 0 h, fun h => by show σ 0 (g 0) = σ 0 c; rw [h]⟩

end TensorCoords

end ListColoring
