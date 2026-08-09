/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.PathColorable
import Monophilic.PathSplit

/-!
# Minimizing list assignments on a path: Lemma 3(b) and 3(c) of Kirov–Naimi

Kirov–Naimi, *List coloring and `n`-monophilic graphs* (arXiv:1004.5183), Lemma 3 concerns an
`(n, n-1)`-**list assignment** for a path `P` of length `k`: one giving `n` colors to each interior
vertex and `n - 1` colors to each of the two terminal vertices. Writing `n = m + 2` throughout, this
is `Monophilic.IsNNAssign k m`. Parts (b) and (c) read:

> (b) `col(P, L) ≥ min(A_k, B_k)` for every `(n, n-1)`-list assignment `L`;
> (c) if `n ≥ 3` and `L` is minimizing, then either `k` is odd and `L` is type A, or `k` is even
> and `L` is type B.

Here `L` is **minimizing** (`SimpleGraph.Minimizing`) when `col(G, L) ≤ col(G, L')` for every `L'`
with `|L'(v)| = |L(v)|` at every vertex, and `A_k`, `B_k` are the recurrences of
`Monophilic.Recurrence`.

## Layout of the proof

* **Existence of a minimizer** (`SimpleGraph.exists_minimizing`). The set of *assignments* is
  infinite — colors range over all of `ℕ` — but the set of achievable *values* `col(G, L')` is a
  nonempty set of naturals, so `Nat.sInf_mem` picks a minimum. No relabelling into a finite palette
  is needed.
* **Shapes** (`Monophilic.IsPathShape`). An `(n, n-1)`-assignment is *shaped* by `(S, x, y)` when
  all its interior lists equal the palette `S`, `|S| = n`, and its terminal lists are `S \ {x}` at
  `pathEnd` and `S \ {y}` at `pathStart`; it is **type A** when `x = y` and **type B** otherwise.
  `Monophilic.col_of_isPathShape` computes the count of any shaped assignment as `A_k` or `B_k`, by
  exhibiting it as a renaming of the canonical `Monophilic.pathAssign` (`exists_palette` plus
  `SimpleGraph.col_image_of_injOn` and `Monophilic.col_pathAssign`).
* **Nestedness** (`Monophilic.nested_of_minimizing`). If a minimizing assignment had incomparable
  lists at the two ends of some edge, cutting the path there (`Monophilic.pathSplitIso`) and
  swapping two colors on one side (`SimpleGraph.col_swapRight_lt`, Lemma 2) would strictly lower the
  count. The two strictness hypotheses need every list of both pieces to have at least two colors,
  which is exactly `n ≥ 3` — for `n = 2` a terminal list has a single color and the argument fails,
  which is why the paper treats `n = 2` separately.
* Nestedness forces all interior lists to coincide and both terminal lists to sit inside them, i.e.
  a shape (`Monophilic.exists_isPathShape_of_minimizing`), whence (b) and (c).

## Deviation from the paper

Part (c) is **false as stated for `k = 0`**, and is proved here under the hypothesis `1 ≤ k`. On the
path of length `0` the two terminal vertices coincide, so an `(n, n-1)`-assignment gives the single
vertex `n - 1` colors; every such assignment is then minimizing, with `n - 1 = A_0` colorings, and
is type A — but `0` is even, so (c) would demand type B. The witness is
`Monophilic.not_parity_of_minimizing_length_zero`. Part (b) is unaffected and is proved for all `k`
and all `n = m + 2` (for `n = 2` it is vacuous: `min(A_k, B_k) = 0`).

## Main results

* `SimpleGraph.Minimizing`, `SimpleGraph.exists_minimizing` : minimizing assignments and their
  existence
* `Monophilic.IsNNAssign`, `Monophilic.IsPathShape` : `(n, n-1)`-assignments and their type A /
  type B shapes
* `Monophilic.col_of_isPathShape` : Lemma 3(a) off the canonical assignment
* `Monophilic.nested_of_minimizing`, `Monophilic.exists_isPathShape_of_minimizing` : a minimizing
  assignment is nested at every edge, hence type A or type B
* `Monophilic.min_pathA_pathB_le_col` : **Lemma 3(b)**
* `Monophilic.col_eq_min_of_minimizing`, `Monophilic.isPathShape_parity_of_minimizing` :
  **Lemma 3(c)**
* `Monophilic.not_parity_of_minimizing_length_zero` : the counterexample to Lemma 3(c) at `k = 0`
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `L` is **minimizing** for `G` when no list assignment with the same list sizes admits fewer
colorings. -/
def Minimizing (G : SimpleGraph V) [DecidableRel G.Adj] (L : ListAssignment V) : Prop :=
  ∀ L' : ListAssignment V, (∀ v, (L' v).card = (L v).card) → G.col L ≤ G.col L'

/-- **A minimizing assignment exists.** -/
theorem exists_minimizing (G : SimpleGraph V) [DecidableRel G.Adj] (L₀ : ListAssignment V) :
    ∃ L : ListAssignment V, (∀ v, (L v).card = (L₀ v).card) ∧ G.Minimizing L := by
  obtain ⟨L, hcard, hcol⟩ := Nat.sInf_mem
    (s := {c : ℕ | ∃ L : ListAssignment V, (∀ v, (L v).card = (L₀ v).card) ∧ G.col L = c})
    ⟨G.col L₀, L₀, fun _ => rfl, rfl⟩
  refine ⟨L, hcard, fun L' hL' => ?_⟩
  rw [hcol]
  exact Nat.sInf_le ⟨L', fun v => (hL' v).trans (hcard v), rfl⟩

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-! ### Numbering the vertices of a path -/

/-- The vertex numbered `i` of the path of length `k`, counting from `pathEnd k` (number `0`)
towards `pathStart k` (number `k`). Indices `> k` are clamped to `pathStart k`. -/
def pathVtx : (k : ℕ) → ℕ → PathV k
  | 0, _ => ()
  | _ + 1, 0 => none
  | k + 1, i + 1 => some (pathVtx k i)

@[simp] lemma pathVtx_succ_succ (k i : ℕ) : pathVtx (k + 1) (i + 1) = some (pathVtx k i) := rfl

lemma pathVtx_zero : ∀ k : ℕ, pathVtx k 0 = pathEnd k
  | 0 => rfl
  | _ + 1 => rfl

lemma pathVtx_last : ∀ k : ℕ, pathVtx k k = pathStart k
  | 0 => rfl
  | k + 1 => congrArg some (pathVtx_last k)

/-- The numbering is injective on `{0, …, k}`. -/
lemma pathVtx_inj : ∀ (k i j : ℕ), i ≤ k → j ≤ k → pathVtx k i = pathVtx k j → i = j := by
  intro k
  induction k with
  | zero => intro i j hi hj _; omega
  | succ k ih =>
    intro i j hi hj h
    match i, j with
    | 0, 0 => rfl
    | 0, j + 1 =>
      have h' : (none : Option (PathV k)) = some (pathVtx k j) := h
      exact absurd h'.symm (Option.some_ne_none _)
    | i + 1, 0 =>
      have h' : (some (pathVtx k i) : Option (PathV k)) = none := h
      exact absurd h' (Option.some_ne_none _)
    | i + 1, j + 1 =>
      have h' : (some (pathVtx k i) : Option (PathV k)) = some (pathVtx k j) := h
      have := ih i j (by omega) (by omega) (Option.some_injective _ h')
      omega

lemma pathVtx_ne_pathEnd {k i : ℕ} (h0 : 0 < i) (hik : i ≤ k) : pathVtx k i ≠ pathEnd k := by
  intro h
  rw [← pathVtx_zero k] at h
  have := pathVtx_inj k i 0 hik (Nat.zero_le k) h
  omega

lemma pathVtx_ne_pathStart {k i : ℕ} (hik : i < k) : pathVtx k i ≠ pathStart k := by
  intro h
  rw [← pathVtx_last k] at h
  have := pathVtx_inj k i k hik.le le_rfl h
  omega

/-! ### The numbering and the splitting isomorphism -/

lemma pathGCongr_pathVtx {m n : ℕ} (h : m = n) (i : ℕ) :
    pathGCongr h (pathVtx m i) = pathVtx n i := by subst h; rfl

lemma pathSplitEquiv_pathVtx_left : ∀ (a b : ℕ),
    pathSplitEquiv a b (pathVtx (b + a + 1) a) = Sum.inl (pathStart a) := by
  intro a
  induction a with
  | zero => intro b; rfl
  | succ a ih =>
    intro b
    show Sum.map some id (pathSplitEquiv a b (pathVtx (b + a + 1) a)) = _
    rw [ih b]
    rfl

lemma pathSplitEquiv_pathVtx_right : ∀ (a b : ℕ),
    pathSplitEquiv a b (pathVtx (b + a + 1) (a + 1)) = Sum.inr (pathEnd b) := by
  intro a
  induction a with
  | zero =>
    intro b
    show Sum.inr (pathVtx b 0) = Sum.inr (pathEnd b)
    rw [pathVtx_zero]
  | succ a ih =>
    intro b
    show Sum.map some id (pathSplitEquiv a b (pathVtx (b + a + 1) (a + 1))) = _
    rw [ih b]
    rfl

/-- The left end of the bridging edge is the vertex numbered `a`. -/
lemma pathSplitIso_pathVtx_left (a b : ℕ) :
    pathSplitIso a b (pathVtx (a + b + 1) a) = Sum.inl (pathStart a) := by
  rw [pathSplitIso_apply, pathGCongr_pathVtx]
  exact pathSplitEquiv_pathVtx_left a b

/-- The right end of the bridging edge is the vertex numbered `a + 1`. -/
lemma pathSplitIso_pathVtx_right (a b : ℕ) :
    pathSplitIso a b (pathVtx (a + b + 1) (a + 1)) = Sum.inr (pathEnd b) := by
  rw [pathSplitIso_apply, pathGCongr_pathVtx]
  exact pathSplitEquiv_pathVtx_right a b

lemma symm_pathSplitIso_inl (a b : ℕ) :
    (pathSplitIso a b).symm (Sum.inl (pathStart a)) = pathVtx (a + b + 1) a := by
  rw [← pathSplitIso_pathVtx_left a b, RelIso.symm_apply_apply]

lemma symm_pathSplitIso_inr (a b : ℕ) :
    (pathSplitIso a b).symm (Sum.inr (pathEnd b)) = pathVtx (a + b + 1) (a + 1) := by
  rw [← pathSplitIso_pathVtx_right a b, RelIso.symm_apply_apply]

/-! ### `(n, n-1)`-list assignments -/

/-- An **`(n, n-1)`-list assignment** for the path of length `k`, with `n = m + 2`: the two terminal
vertices get `n - 1 = m + 1` colors and every interior vertex gets `n = m + 2` colors.

For `k = 0` the two terminal vertices coincide and the single vertex gets `m + 1` colors. -/
structure IsNNAssign (k m : ℕ) (L : ListAssignment (PathV k)) : Prop where
  card_pathEnd : (L (pathEnd k)).card = m + 1
  card_pathStart : (L (pathStart k)).card = m + 1
  card_interior : ∀ v, v ≠ pathEnd k → v ≠ pathStart k → (L v).card = m + 2

/-- For `n ≥ 3` every list of an `(n, n-1)`-assignment has at least two colors. -/
lemma IsNNAssign.two_le_card {k m : ℕ} {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L)
    (hm : 1 ≤ m) (v : PathV k) : 2 ≤ (L v).card := by
  by_cases h1 : v = pathEnd k
  · rw [h1, hL.card_pathEnd]; omega
  by_cases h2 : v = pathStart k
  · rw [h2, hL.card_pathStart]; omega
  · rw [hL.card_interior v h1 h2]; omega

/-- Two `(n, n-1)`-assignments on the same path have the same list sizes. -/
lemma IsNNAssign.card_eq {k m : ℕ} {L L' : ListAssignment (PathV k)} (hL : IsNNAssign k m L)
    (hL' : IsNNAssign k m L') (v : PathV k) : (L' v).card = (L v).card := by
  by_cases h1 : v = pathEnd k
  · rw [h1, hL.card_pathEnd, hL'.card_pathEnd]
  by_cases h2 : v = pathStart k
  · rw [h2, hL.card_pathStart, hL'.card_pathStart]
  · rw [hL.card_interior v h1 h2, hL'.card_interior v h1 h2]

/-! ### Renaming a palette

The canonical `(n, n-1)`-assignments `pathAssign k n x y` use the palette `range n`. An arbitrary
palette `S` of `n` colors is the image of `range n` under a function injective on `range n`, so
`SimpleGraph.col_image_of_injOn` transports the count. -/

/-- `Finset.image` commutes with `Finset.erase` for a function injective on the ambient set. -/
lemma image_erase_of_injOn {S : Finset ℕ} {e : ℕ → ℕ} (hinj : Set.InjOn e ↑S) {x : ℕ} (hx : x ∈ S) :
    (S.erase x).image e = (S.image e).erase (e x) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨a, ⟨hax, haS⟩, rfl⟩
    exact ⟨fun h => hax (hinj (Finset.mem_coe.mpr haS) (Finset.mem_coe.mpr hx) h), a, haS, rfl⟩
  · rintro ⟨hz, a, ha, rfl⟩
    exact ⟨a, ⟨fun h => hz (by rw [h]), ha⟩, rfl⟩

/-- Any `n`-element set of colors is a renaming of the standard palette `range n`. -/
lemma exists_palette {S : Finset ℕ} {n : ℕ} (hS : S.card = n) :
    ∃ e : ℕ → ℕ, Set.InjOn e ↑(range n) ∧ (range n).image e = S := by
  classical
  refine ⟨fun i => if h : i < n then ((S.orderIsoOfFin hS) ⟨i, h⟩ : ℕ) else 0, ?_, ?_⟩
  · intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only [dif_pos ha, dif_pos hb] at hab
    have h : ((S.orderIsoOfFin hS) ⟨a, ha⟩ : S) = (S.orderIsoOfFin hS) ⟨b, hb⟩ := Subtype.ext hab
    simpa using (S.orderIsoOfFin hS).injective h
  · ext z
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [dif_pos hi]
      exact ((S.orderIsoOfFin hS) ⟨i, hi⟩).2
    · intro hz
      refine ⟨((S.orderIsoOfFin hS).symm ⟨z, hz⟩ : Fin n).val, Fin.is_lt _, ?_⟩
      simp only [dif_pos (Fin.is_lt _)]
      simp

/-! ### The canonical assignments -/

lemma pathInterior_subset (n y : ℕ) : ∀ (k : ℕ) (v : PathV k), pathInterior k n y v ⊆ range n := by
  intro k
  induction k with
  | zero => exact fun _ _ hz => Finset.mem_of_mem_erase hz
  | succ k ih =>
    intro v
    match v with
    | none => exact fun _ hz => hz
    | some w => exact ih w

lemma pathAssign_subset (n x y : ℕ) :
    ∀ (k : ℕ) (v : PathV k), pathAssign k n x y v ⊆ range n := by
  intro k
  match k with
  | 0 => exact fun _ _ hz => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  | k + 1 =>
    intro v
    match v with
    | none => exact fun _ hz => Finset.mem_of_mem_erase hz
    | some w => exact pathInterior_subset n y k w

/-- The list at the far end of a `pathInterior` block. -/
lemma pathInterior_pathStart (n y : ℕ) :
    ∀ k : ℕ, pathInterior k n y (pathStart k) = (range n).erase y := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- Every other vertex of a `pathInterior` block carries the full palette. -/
lemma pathInterior_of_ne (n y : ℕ) :
    ∀ (k : ℕ) (v : PathV k), v ≠ pathStart k → pathInterior k n y v = range n := by
  intro k
  induction k with
  | zero => intro v hv; exact absurd (Subsingleton.elim v (pathStart 0)) hv
  | succ k ih =>
    intro v hv
    match v with
    | none => rfl
    | some w =>
      refine ih w fun h => hv ?_
      show (some w : Option (PathV k)) = some (pathStart k)
      rw [h]

/-- The canonical `(n, n-1)`-assignment really is one, as soon as the path has an edge. -/
lemma isNNAssign_pathAssign (j m x y : ℕ) (hx : x < m + 2) (hy : y < m + 2) :
    IsNNAssign (j + 1) m (pathAssign (j + 1) (m + 2) x y) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((range (m + 2)).erase x).card = m + 1
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hx), Finset.card_range]
    omega
  · show (pathInterior j (m + 2) y (pathStart j)).card = m + 1
    rw [pathInterior_pathStart, Finset.card_erase_of_mem (Finset.mem_range.mpr hy),
      Finset.card_range]
    omega
  · intro v h1 h2
    match v with
    | none => exact absurd rfl h1
    | some w =>
      show (pathInterior j (m + 2) y w).card = m + 2
      rw [pathInterior_of_ne _ _ _ w fun h => h2 (congrArg some h), Finset.card_range]

/-! ### Type A and type B assignments, up to renaming of the colors

This is Lemma 3(a) off the canonical assignment: an `(n, n-1)`-assignment whose interior lists are
all equal to a palette `S` is a renaming of `pathAssign k n x y`, hence counted by `A_k` or `B_k`. -/

/-- The shape of the `(n, n-1)`-list assignments of Lemma 3, with `n = m + 2`: the interior lists
are all equal to a common palette `S` of `n` colors, the list at `pathEnd k` is `S \ {x}` and the
list at `pathStart k` is `S \ {y}`, with `x, y ∈ S`. Such an `L` is **type A** when `x = y` and
**type B** when `x ≠ y`.

For `k = 0` the two terminal vertices coincide, so the two conditions force `x = y`: a path of
length `0` carries only type A assignments. -/
structure IsPathShape (k m : ℕ) (L : ListAssignment (PathV k)) (S : Finset ℕ) (x y : ℕ) :
    Prop where
  card_palette : S.card = m + 2
  mem_left : x ∈ S
  mem_right : y ∈ S
  apply_pathEnd : L (pathEnd k) = S.erase x
  apply_pathStart : L (pathStart k) = S.erase y
  apply_interior : ∀ i, 0 < i → i < k → L (pathVtx k i) = S

/-- Every vertex of the path of length `k` is numbered. -/
lemma exists_pathVtx : ∀ (k : ℕ) (v : PathV k), ∃ i, i ≤ k ∧ pathVtx k i = v := by
  intro k
  induction k with
  | zero => intro v; exact ⟨0, le_rfl, Subsingleton.elim _ v⟩
  | succ k ih =>
    intro v
    match v with
    | none => exact ⟨0, by omega, rfl⟩
    | some w =>
      obtain ⟨i, hi, hiw⟩ := ih w
      exact ⟨i + 1, by omega, congrArg some hiw⟩

/-- A shaped assignment is an `(n, n-1)`-assignment, as soon as the path has an edge. -/
lemma IsPathShape.isNNAssign {k m : ℕ} {L : ListAssignment (PathV k)} {S : Finset ℕ} {x y : ℕ}
    (h : IsPathShape k m L S x y) : IsNNAssign k m L := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.apply_pathEnd, Finset.card_erase_of_mem h.mem_left, h.card_palette]
    omega
  · rw [h.apply_pathStart, Finset.card_erase_of_mem h.mem_right, h.card_palette]
    omega
  · intro v h1 h2
    obtain ⟨i, hik, rfl⟩ := exists_pathVtx k v
    have h0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · exact absurd (hi ▸ pathVtx_zero k) h1
      · exact hi
    have hlt : i < k := by
      rcases Nat.lt_or_ge i k with hi | hi
      · exact hi
      · exact absurd ((Nat.le_antisymm hik hi) ▸ pathVtx_last k) h2
    rw [h.apply_interior i h0 hlt, h.card_palette]

/-- `S.erase` is injective on the elements of `S`. -/
lemma eq_of_erase_eq_erase {S : Finset ℕ} {x y : ℕ} (hy : y ∈ S) (h : S.erase x = S.erase y) :
    x = y := by
  by_contra hne
  have hmem : y ∈ S.erase x := Finset.mem_erase.mpr ⟨fun hh => hne hh.symm, hy⟩
  rw [h] at hmem
  exact (Finset.mem_erase.mp hmem).1 rfl

/-- **A path of length `0` carries no type B assignment**: its two terminal vertices coincide, so
the two conditions on the terminal lists force `x = y`. -/
lemma IsPathShape.eq_of_length_zero {m : ℕ} {L : ListAssignment (PathV 0)} {S : Finset ℕ}
    {x y : ℕ} (h : IsPathShape 0 m L S x y) : x = y := by
  refine eq_of_erase_eq_erase h.mem_right ?_
  rw [← h.apply_pathEnd, ← h.apply_pathStart]
  rfl

/-- Recognising a renamed `pathInterior` block from its values at the numbered vertices. -/
private lemma eq_image_pathInterior {n y' : ℕ} {e : ℕ → ℕ} :
    ∀ (k : ℕ) (L : ListAssignment (PathV k)),
      (∀ i, i < k → L (pathVtx k i) = (range n).image e) →
      L (pathStart k) = ((range n).erase y').image e →
      ∀ v, L v = (pathInterior k n y' v).image e := by
  intro k
  induction k with
  | zero =>
    intro L _ hstart v
    rw [Subsingleton.elim v (pathStart 0)]
    exact hstart
  | succ k ih =>
    intro L hint hstart v
    match v with
    | none => exact hint 0 (by omega)
    | some w =>
      exact ih (fun u => L (some u)) (fun i hi => hint (i + 1) (by omega)) hstart w

/-- Recognising a renamed `pathAssign` from its values at the numbered vertices. -/
private lemma eq_image_pathAssign {n : ℕ} {k : ℕ} {L : ListAssignment (PathV k)} {x' y' : ℕ}
    {e : ℕ → ℕ} (hzero : k = 0 → x' = y')
    (hEnd : L (pathEnd k) = ((range n).erase x').image e)
    (hStart : L (pathStart k) = ((range n).erase y').image e)
    (hInt : ∀ i, 0 < i → i < k → L (pathVtx k i) = (range n).image e) :
    ∀ v, L v = (pathAssign k n x' y' v).image e := by
  match k with
  | 0 =>
    intro v
    obtain rfl := hzero rfl
    rw [Subsingleton.elim v (pathEnd 0)]
    show L (pathEnd 0) = (((range n).erase x').erase x').image e
    rw [Finset.erase_idem]
    exact hEnd
  | j + 1 =>
    intro v
    match v with
    | none => exact hEnd
    | some w =>
      exact eq_image_pathInterior j (fun u => L (some u))
        (fun i hi => hInt (i + 1) (by omega) (by omega)) hStart w

/-- **Lemma 3(a), off the canonical assignment.** A type A shaped assignment on the path of length
`k` admits `A_k` colorings, and a type B shaped one admits `B_k`. -/
theorem col_of_isPathShape {k m : ℕ} {L : ListAssignment (PathV k)} {S : Finset ℕ} {x y : ℕ}
    (h : IsPathShape k m L S x y) :
    (pathG k).col L = if x = y then pathA m k else pathB m k := by
  obtain ⟨e, hinj, himg⟩ := exists_palette h.card_palette
  obtain ⟨x', hx', hex⟩ : ∃ x' ∈ range (m + 2), e x' = x := by
    refine Finset.mem_image.mp ?_
    rw [himg]; exact h.mem_left
  obtain ⟨y', hy', hey⟩ : ∃ y' ∈ range (m + 2), e y' = y := by
    refine Finset.mem_image.mp ?_
    rw [himg]; exact h.mem_right
  have hiff : x' = y' ↔ x = y := by
    constructor
    · intro hh; rw [← hex, ← hey, hh]
    · intro hh
      exact hinj (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy') (by rw [hex, hey, hh])
  have hEnd : L (pathEnd k) = ((range (m + 2)).erase x').image e := by
    rw [image_erase_of_injOn hinj hx', himg, hex, h.apply_pathEnd]
  have hStart : L (pathStart k) = ((range (m + 2)).erase y').image e := by
    rw [image_erase_of_injOn hinj hy', himg, hey, h.apply_pathStart]
  have hInt : ∀ i, 0 < i → i < k → L (pathVtx k i) = (range (m + 2)).image e := by
    intro i h0 hik
    rw [himg, h.apply_interior i h0 hik]
  have hzero : k = 0 → x' = y' := by
    intro hk0
    subst hk0
    exact hiff.mpr h.eq_of_length_zero
  have key := eq_image_pathAssign hzero hEnd hStart hInt
  have hsub : (⋃ v, ((pathAssign k (m + 2) x' y' v : Finset ℕ) : Set ℕ)) ⊆ ↑(range (m + 2)) := by
    refine Set.iUnion_subset fun v z hz => ?_
    exact Finset.mem_coe.mpr (pathAssign_subset (m + 2) x' y' k v (Finset.mem_coe.mp hz))
  have hcol : (pathG k).col L = (pathG k).col (pathAssign k (m + 2) x' y') := by
    rw [funext key]
    exact col_image_of_injOn (hinj.mono hsub)
  rw [hcol, col_pathAssign m k x' y' (Finset.mem_range.mp hx') (Finset.mem_range.mp hy')]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos (hiff.mpr hxy)]
  · rw [if_neg hxy, if_neg fun hh => hxy (hiff.mp hh)]

/-! ### A minimizing assignment is nested at every edge

This is the heart of Lemma 3(c). If the lists at the two ends of some edge are incomparable, cut
the path there (`Monophilic.pathSplitIso`) and apply the strict form of the swap step
(`SimpleGraph.col_swapRight_lt`) of Lemma 2. Its two strictness hypotheses hold because each side
of the cut is a path all of whose lists have at least two colors — which is exactly where `n ≥ 3`
is needed. -/

/-- **A minimizing assignment is nested at every edge.** -/
theorem nested_of_minimizing {k : ℕ} {L : ListAssignment (PathV k)}
    (hmin : (pathG k).Minimizing L) (hcard : ∀ v, 2 ≤ (L v).card) {a b : ℕ} (hab : k = a + b + 1) :
    L (pathVtx k a) ⊆ L (pathVtx k (a + 1)) ∨ L (pathVtx k (a + 1)) ⊆ L (pathVtx k a) := by
  subst hab
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  obtain ⟨c₁, hc₁, hc₁'⟩ := Finset.not_subset.mp h1
  obtain ⟨c₂, hc₂, hc₂'⟩ := Finset.not_subset.mp h2
  set M : ListAssignment (PathV a ⊕ PathV b) := L ∘ (pathSplitIso a b).symm with hM
  have hMl : M (Sum.inl (pathStart a)) = L (pathVtx (a + b + 1) a) :=
    congrArg L (symm_pathSplitIso_inl a b)
  have hMr : M (Sum.inr (pathEnd b)) = L (pathVtx (a + b + 1) (a + 1)) :=
    congrArg L (symm_pathSplitIso_inr a b)
  have hG : (pathG a).colFix (M ∘ Sum.inl) (pathStart a) c₁ ≠ 0 := by
    have hpos := colFix_pos_of_two_le_card a (M ∘ Sum.inl) (fun u => hcard _) (pathStart a) c₁
      (by show c₁ ∈ M (Sum.inl (pathStart a)); rw [hMl]; exact hc₁)
    omega
  have hH : (pathG b).colFix (M ∘ Sum.inr) (pathEnd b) c₂ ≠ 0 := by
    have hpos := colFix_pos_of_two_le_card b (M ∘ Sum.inr) (fun u => hcard _) (pathEnd b) c₂
      (by show c₂ ∈ M (Sum.inr (pathEnd b)); rw [hMr]; exact hc₂)
    omega
  have hlt : (bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)).col (swapRight M c₁ c₂)
      < (bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)).col M :=
    col_swapRight_lt M (by rw [hMl]; exact hc₁) (by rw [hMr]; exact hc₁')
      (by rw [hMl]; exact hc₂') hG hH
  have hcolL : (pathG (a + b + 1)).col L
      = (bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)).col M := col_pathG_split a b L
  have hcolL' : (pathG (a + b + 1)).col (swapRight M c₁ c₂ ∘ pathSplitIso a b)
      = (bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)).col (swapRight M c₁ c₂) :=
    col_bridge_pathSplit a b _
  have hcards : ∀ v, ((swapRight M c₁ c₂ ∘ pathSplitIso a b) v).card = (L v).card := by
    intro v
    show (swapRight M c₁ c₂ (pathSplitIso a b v)).card = (L v).card
    rw [card_swapRight]
    show (L ((pathSplitIso a b).symm (pathSplitIso a b v))).card = (L v).card
    rw [RelIso.symm_apply_apply]
  have hge := hmin _ hcards
  omega

/-- **The interior lists of a minimizing assignment all coincide.** -/
theorem interior_eq_of_minimizing {k m : ℕ} (hm : 1 ≤ m) {L : ListAssignment (PathV k)}
    (hL : IsNNAssign k m L) (hmin : (pathG k).Minimizing L) :
    ∀ i, 0 < i → i < k → L (pathVtx k i) = L (pathVtx k 1) := by
  have hcard := hL.two_le_card hm
  have hint : ∀ i, 0 < i → i < k → (L (pathVtx k i)).card = m + 2 := fun i h0 hik =>
    hL.card_interior _ (pathVtx_ne_pathEnd h0 hik.le) (pathVtx_ne_pathStart hik)
  intro i
  induction i with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ i ih =>
    intro _ hik
    match i with
    | 0 => rfl
    | i + 1 =>
      have hIH := ih (by omega) (by omega)
      have hn : L (pathVtx k (i + 1)) ⊆ L (pathVtx k (i + 2)) ∨
          L (pathVtx k (i + 2)) ⊆ L (pathVtx k (i + 1)) :=
        nested_of_minimizing hmin hcard (a := i + 1) (b := k - (i + 2)) (by omega)
      have hc1 := hint (i + 1) (by omega) (by omega)
      have hc2 := hint (i + 2) (by omega) (by omega)
      have heq : L (pathVtx k (i + 2)) = L (pathVtx k (i + 1)) := by
        rcases hn with h | h
        · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
        · exact Finset.eq_of_subset_of_card_le h (by omega)
      exact heq.trans hIH

/-! ### Lemma 3(c): a minimizing assignment is type A or type B -/

lemma exists_notMem (T : Finset ℕ) : ∃ z, z ∉ T := by
  refine ⟨T.sup id + 1, fun h => ?_⟩
  have hle := Finset.le_sup (f := id) h
  simp only [id_eq] at hle
  omega

/-- A subset with one element fewer is the complement of a single point. -/
lemma exists_eq_erase {T S : Finset ℕ} (hsub : T ⊆ S) (hcard : T.card + 1 = S.card) :
    ∃ x ∈ S, T = S.erase x := by
  have h1 : (S \ T).card = 1 := by rw [Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
  have hxmem : x ∈ S \ T := by rw [hx]; exact Finset.mem_singleton_self x
  rw [Finset.mem_sdiff] at hxmem
  refine ⟨x, hxmem.1, ?_⟩
  ext z
  simp only [Finset.mem_erase]
  constructor
  · intro hz
    exact ⟨fun h => hxmem.2 (h ▸ hz), hsub hz⟩
  · rintro ⟨hzx, hzS⟩
    by_contra hzT
    have hmem : z ∈ S \ T := Finset.mem_sdiff.mpr ⟨hzS, hzT⟩
    rw [hx, Finset.mem_singleton] at hmem
    exact hzx hmem

/-- **Lemma 3(c), structural half.** For `n ≥ 3`, a minimizing `(n, n-1)`-list assignment on a path
is type A or type B: its interior lists are all equal to a palette `S` of `n` colors and its two
terminal lists are `S` minus one color each. -/
theorem exists_isPathShape_of_minimizing {k m : ℕ} (hm : 1 ≤ m) {L : ListAssignment (PathV k)}
    (hL : IsNNAssign k m L) (hmin : (pathG k).Minimizing L) :
    ∃ S x y, IsPathShape k m L S x y := by
  have hcard2 := hL.two_le_card hm
  match k with
  | 0 =>
    obtain ⟨z, hz⟩ := exists_notMem (L (pathEnd 0))
    refine ⟨insert z (L (pathEnd 0)), z, z, ?_, Finset.mem_insert_self _ _,
      Finset.mem_insert_self _ _, (Finset.erase_insert hz).symm, (Finset.erase_insert hz).symm,
      fun i h0 hik => absurd hik (by omega)⟩
    rw [Finset.card_insert_of_notMem hz, hL.card_pathEnd]
  | 1 =>
    have hn : L (pathVtx 1 0) ⊆ L (pathVtx 1 1) ∨ L (pathVtx 1 1) ⊆ L (pathVtx 1 0) :=
      nested_of_minimizing hmin hcard2 (a := 0) (b := 0) (by omega)
    rw [pathVtx_zero, pathVtx_last] at hn
    have heq : L (pathEnd 1) = L (pathStart 1) := by
      have h1 := hL.card_pathEnd
      have h2 := hL.card_pathStart
      rcases hn with h | h
      · exact Finset.eq_of_subset_of_card_le h (by omega)
      · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
    obtain ⟨z, hz⟩ := exists_notMem (L (pathEnd 1))
    refine ⟨insert z (L (pathEnd 1)), z, z, ?_, Finset.mem_insert_self _ _,
      Finset.mem_insert_self _ _, (Finset.erase_insert hz).symm, ?_,
      fun i h0 hik => absurd hik (by omega)⟩
    · rw [Finset.card_insert_of_notMem hz, hL.card_pathEnd]
    · rw [← heq, Finset.erase_insert hz]
  | j + 2 =>
    have hint := interior_eq_of_minimizing hm hL hmin
    have hcardS : (L (pathVtx (j + 2) 1)).card = m + 2 :=
      hL.card_interior _ (pathVtx_ne_pathEnd (by omega) (by omega))
        (pathVtx_ne_pathStart (by omega))
    -- the list at `pathEnd` is contained in the palette
    have hn0 : L (pathVtx (j + 2) 0) ⊆ L (pathVtx (j + 2) 1) ∨
        L (pathVtx (j + 2) 1) ⊆ L (pathVtx (j + 2) 0) :=
      nested_of_minimizing hmin hcard2 (a := 0) (b := j + 1) (by omega)
    rw [pathVtx_zero] at hn0
    have hsub0 : L (pathEnd (j + 2)) ⊆ L (pathVtx (j + 2) 1) := by
      rcases hn0 with h | h
      · exact h
      · have := Finset.card_le_card h
        rw [hL.card_pathEnd, hcardS] at this
        omega
    obtain ⟨x, hxS, hx⟩ := exists_eq_erase hsub0 (by rw [hL.card_pathEnd, hcardS])
    -- and so is the list at `pathStart`
    have hn1 : L (pathVtx (j + 2) (j + 1)) ⊆ L (pathVtx (j + 2) (j + 2)) ∨
        L (pathVtx (j + 2) (j + 2)) ⊆ L (pathVtx (j + 2) (j + 1)) :=
      nested_of_minimizing hmin hcard2 (a := j + 1) (b := 0) (by omega)
    rw [pathVtx_last, hint (j + 1) (by omega) (by omega)] at hn1
    have hsub1 : L (pathStart (j + 2)) ⊆ L (pathVtx (j + 2) 1) := by
      rcases hn1 with h | h
      · have := Finset.card_le_card h
        rw [hL.card_pathStart, hcardS] at this
        omega
      · exact h
    obtain ⟨y, hyS, hy⟩ := exists_eq_erase hsub1 (by rw [hL.card_pathStart, hcardS])
    exact ⟨L (pathVtx (j + 2) 1), x, y, hcardS, hxS, hyS, hx, hy, hint⟩

/-! ### Lemma 3(b) and Lemma 3(c) -/

/-- For `n = 2` one of `A_k`, `B_k` always vanishes. -/
lemma min_pathA_pathB_zero : ∀ k : ℕ, min (pathA 0 k) (pathB 0 k) = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pathA_succ, pathB_succ]
    omega

/-- **Lemma 3(b) of Kirov–Naimi.** Every `(n, n-1)`-list assignment on the path of length `k`
admits at least `min (A_k, B_k)` colorings. -/
theorem min_pathA_pathB_le_col {k m : ℕ} {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L) :
    min (pathA m k) (pathB m k) ≤ (pathG k).col L := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [min_pathA_pathB_zero]
    exact Nat.zero_le _
  obtain ⟨L', hcard, hmin⟩ := exists_minimizing (pathG k) L
  have hL' : IsNNAssign k m L' :=
    ⟨by rw [hcard]; exact hL.card_pathEnd, by rw [hcard]; exact hL.card_pathStart,
      fun v h1 h2 => by rw [hcard]; exact hL.card_interior v h1 h2⟩
  obtain ⟨S, x, y, hshape⟩ := exists_isPathShape_of_minimizing hm hL' hmin
  refine le_trans ?_ (hmin L fun v => (hcard v).symm)
  rw [col_of_isPathShape hshape]
  split
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- **A minimizing assignment realizes the minimum.** For `n ≥ 3` and a path with at least one
edge, a minimizing `(n, n-1)`-list assignment admits exactly `min (A_k, B_k)` colorings. -/
theorem col_eq_min_of_minimizing {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L) (hmin : (pathG k).Minimizing L) :
    (pathG k).col L = min (pathA m k) (pathB m k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hleA : (pathG (j + 1)).col L ≤ pathA m (j + 1) := by
    have h := hmin (pathAssign (j + 1) (m + 2) 0 0)
      (IsNNAssign.card_eq hL (isNNAssign_pathAssign j m 0 0 (by omega) (by omega)))
    rwa [col_pathAssign m (j + 1) 0 0 (by omega) (by omega), if_pos rfl] at h
  have hleB : (pathG (j + 1)).col L ≤ pathB m (j + 1) := by
    have h := hmin (pathAssign (j + 1) (m + 2) 0 1)
      (IsNNAssign.card_eq hL (isNNAssign_pathAssign j m 0 1 (by omega) (by omega)))
    rwa [col_pathAssign m (j + 1) 0 1 (by omega) (by omega), if_neg (by omega)] at h
  exact le_antisymm (le_min hleA hleB) (min_pathA_pathB_le_col hL)

/-- **Lemma 3(c) of Kirov–Naimi.** For `n ≥ 3` and a path with at least one edge, a minimizing
`(n, n-1)`-list assignment is type A when `k` is odd and type B when `k` is even.

The hypothesis `1 ≤ k` cannot be dropped; see `Monophilic.not_parity_of_minimizing_length_zero`. -/
theorem isPathShape_parity_of_minimizing {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L) (hmin : (pathG k).Minimizing L) :
    ∃ S x y, IsPathShape k m L S x y ∧ ((Odd k ∧ x = y) ∨ (Even k ∧ x ≠ y)) := by
  obtain ⟨S, x, y, hshape⟩ := exists_isPathShape_of_minimizing hm hL hmin
  have hcol := col_of_isPathShape hshape
  have hmincol := col_eq_min_of_minimizing hm hk hL hmin
  refine ⟨S, x, y, hshape, ?_⟩
  by_cases hev : Even k
  · refine Or.inr ⟨hev, fun hxy => ?_⟩
    rw [if_pos hxy] at hcol
    have hlt := pathB_lt_pathA hev m
    rw [min_eq_right hlt.le] at hmincol
    omega
  · refine Or.inl ⟨Nat.not_even_iff_odd.mp hev, ?_⟩
    by_contra hxy
    rw [if_neg hxy] at hcol
    have hlt := pathA_lt_pathB (Nat.not_even_iff_odd.mp hev) m
    rw [min_eq_left hlt.le] at hmincol
    omega

/-! ### The parity statement genuinely needs `1 ≤ k`

On the path of length `0` the two terminal vertices coincide, so an `(n, n-1)`-assignment gives the
single vertex `n - 1` colors and *every* such assignment is minimizing — with `n - 1 = A_0`
colorings, not `B_0 = n - 2`. Correspondingly, every shape on a path of length `0` is type A
(`Monophilic.IsPathShape.eq_of_length_zero`), while `0` is even. So the conclusion of Lemma 3(c),
read at `k = 0`, is false; the witness below is `n = 3` with the list `{0, 1}`. -/

/-- **A counterexample to Lemma 3(c) at `k = 0`.** -/
theorem not_parity_of_minimizing_length_zero :
    ∃ L : ListAssignment (PathV 0), IsNNAssign 0 1 L ∧ (pathG 0).Minimizing L ∧
      ¬ ∃ S x y, IsPathShape 0 1 L S x y ∧ ((Odd 0 ∧ x = y) ∨ (Even 0 ∧ x ≠ y)) := by
  refine ⟨fun _ => {0, 1}, ⟨rfl, rfl, fun v h1 _ => absurd (Subsingleton.elim v (pathEnd 0)) h1⟩,
    ?_, ?_⟩
  · intro L' hL'
    rw [col_pathG_zero, col_pathG_zero, hL' default]
  · rintro ⟨S, x, y, hshape, hcase | hcase⟩
    · obtain ⟨r, hr⟩ := hcase.1
      omega
    · exact hcase.2 hshape.eq_of_length_zero

/-! ### Numerical cross-check

The identifications above, checked at `n = 3` against explicitly enumerated colorings. -/

/-- The `(3, 2)`-assignment with palette `{0, 1, 2}` missing `x` at `pathEnd` and `y` at
`pathStart`; type A when `x = y`. -/
private def testAssign (k x y : ℕ) : ListAssignment (PathV k) := fun v =>
  if v = pathEnd k then ({0, 1, 2} : Finset ℕ).erase x
  else if v = pathStart k then ({0, 1, 2} : Finset ℕ).erase y
  else ({0, 1, 2} : Finset ℕ)

-- `col_of_isPathShape`: shaped assignments are counted by `A_k` and `B_k`
#guard (pathG 2).col (testAssign 2 0 0) == pathA 1 2   -- `A₂ = 6`
#guard (pathG 2).col (testAssign 2 0 1) == pathB 1 2   -- `B₂ = 5`
#guard (pathG 3).col (testAssign 3 0 0) == pathA 1 3   -- `A₃ = 10`
#guard (pathG 3).col (testAssign 3 0 1) == pathB 1 3   -- `B₃ = 11`

/-- A `(3, 2)`-assignment that is *not* nested at the edge `0-1`, hence not minimizing. -/
private def testNonNested : ListAssignment (PathV 2) := fun v =>
  if v = pathVtx 2 0 then ({0, 1} : Finset ℕ)
  else if v = pathVtx 2 2 then ({2, 3} : Finset ℕ) else ({1, 2, 3} : Finset ℕ)

-- `min_pathA_pathB_le_col`: Lemma 3(b), here with room to spare
#guard min (pathA 1 2) (pathB 1 2) ≤ (pathG 2).col testNonNested   -- `5 ≤ 6`

end Monophilic
