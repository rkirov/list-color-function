/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Rename

/-!
# Basic theory of `col` and enumerative chromatic-choosability

This file connects `col` to Mathlib's `SimpleGraph.Colorable`, introduces choosability, proves the
elementary "regime" facts of Kirov–Naimi §1, and sets up the prescribed-color API
(`col(G, L, v, c)` in the paper's notation) on which Lemmas 2, 3 and Theorem 1 all rely.

## Main results

* `SimpleGraph.colConst_pos_iff_colorable` : `0 < col(G, n) ↔ G.Colorable n`
* `SimpleGraph.ecc_of_not_colorable` : if `n < χ(G)` then `G` is enumeratively chromatic-choosable
  at `n`
* `SimpleGraph.not_ecc_of_colorable_of_not_choosable` : if `χ(G) ≤ n < χ_ℓ(G)` then `G` is
  not enumeratively chromatic-choosable at `n`
* `SimpleGraph.choosable_of_ecc_of_colorable`, `SimpleGraph.ECC.choosable` : enumeratively
  chromatic-choosable implies chromatic-choosable — the implication the name is built on
* `SimpleGraph.colorable_of_choosable` : `χ(G) ≤ χ_ℓ(G)`
* `SimpleGraph.sum_colFix` : `col(G, L) = ∑ c ∈ L v, col(G, L, v, c)`
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Bridge to Mathlib's `Colorable` -/

/-- A graph has a coloring from the constant list `{0, …, n-1}` exactly when it is `n`-colorable. -/
theorem colConst_pos_iff_colorable {n : ℕ} : 0 < G.colConst n ↔ G.Colorable n := by
  rw [colConst, col_pos_iff]
  constructor
  · rintro ⟨f, hf⟩
    rw [mem_colorings] at hf
    refine ⟨Coloring.mk (fun v => ⟨f v, Finset.mem_range.mp (hf.1 v)⟩) ?_⟩
    intro v w hvw hcon
    exact hf.2 hvw (congrArg Fin.val hcon)
  · rintro ⟨C⟩
    refine ⟨fun v => (C v : ℕ), ?_⟩
    rw [mem_colorings]
    refine ⟨fun v => Finset.mem_range.mpr (C v).isLt, ?_⟩
    intro v w hvw hcon
    exact C.valid hvw (Fin.val_injective hcon)

theorem colConst_eq_zero_iff_not_colorable {n : ℕ} : G.colConst n = 0 ↔ ¬ G.Colorable n := by
  rw [← colConst_pos_iff_colorable, Nat.pos_iff_ne_zero]
  exact not_not.symm

/-! ### Choosability -/

/-- `G` is **`n`-choosable** if it admits a coloring from every `n`-list assignment. This is the
paper's `n`-choosable (a.k.a. `n`-list colorable); `χ_ℓ(G) ≤ n` iff `G` is `n`-choosable. -/
def Choosable (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → 0 < G.col L

/-- `χ(G) ≤ χ_ℓ(G)`: an `n`-choosable graph is `n`-colorable. This is item (1) of the list on
p. 2 of the paper. -/
theorem colorable_of_choosable {n : ℕ} (h : G.Choosable n) : G.Colorable n :=
  colConst_pos_iff_colorable.mp (h _ (isNListAssignment_constList n))

/-! ### The three regimes (Kirov–Naimi p. 2) -/

/-- Item (2): if `n < χ(G)` then `G` is enumeratively chromatic-choosable at `n`, vacuously —
there are no colorings at all from the constant list. -/
theorem ecc_of_not_colorable {n : ℕ} (h : ¬ G.Colorable n) : G.ECCAt n := by
  intro L _
  rw [colConst_eq_zero_iff_not_colorable.mpr h]
  exact Nat.zero_le _

/-- Item (3): if `χ(G) ≤ n < χ_ℓ(G)` then `G` is *not* enumeratively chromatic-choosable at `n`. -/
theorem not_ecc_of_colorable_of_not_choosable {n : ℕ}
    (hcol : G.Colorable n) (hch : ¬ G.Choosable n) : ¬ G.ECCAt n := by
  intro hmono
  rw [Choosable] at hch
  push Not at hch
  obtain ⟨L, hL, hzero⟩ := hch
  have h0 : G.col L = 0 := Nat.le_zero.mp hzero
  have := hmono L hL
  rw [h0] at this
  exact absurd (colConst_pos_iff_colorable.mpr hcol) (Nat.not_lt.mpr this)

/-- Conversely, an `n`-colorable graph that is enumeratively chromatic-choosable at `n` is
`n`-choosable. -/
theorem choosable_of_ecc_of_colorable {n : ℕ}
    (hmono : G.ECCAt n) (hcol : G.Colorable n) : G.Choosable n :=
  fun L hL => lt_of_lt_of_le (colConst_pos_iff_colorable.mpr hcol) (hmono L hL)

/-- **Enumeratively chromatic-choosable implies chromatic-choosable**, which is what justifies the
name: an enumeratively chromatic-choosable graph is `n`-choosable for every `n` it is
`n`-colorable at, so `χ_ℓ(G) = χ(G)` — Ohba's *chromatic-choosable*. -/
theorem ECC.choosable {n : ℕ} (h : G.ECC) (hcol : G.Colorable n) : G.Choosable n :=
  choosable_of_ecc_of_colorable (h.eccAt n) hcol

/-! ### Prescribing colors at a vertex

The paper writes `col(G, L, v₁, c₁, …, v_k, c_k)` for the number of colorings of `G` from `L` that
assign `cᵢ` to `vᵢ`. We introduce the one-vertex case, which is what the arguments actually use,
together with the fibrewise decomposition of `col`. -/

/-- `col(G, L, v, c)`: the number of colorings of `G` from `L` assigning color `c` to vertex `v`. -/
def colFix (G : SimpleGraph V) [DecidableRel G.Adj] (L : ListAssignment V) (v : V) (c : ℕ) : ℕ :=
  ((G.colorings L).filter (fun f => f v = c)).card

@[simp] lemma colFix_eq_zero_of_notMem {L : ListAssignment V} {v : V} {c : ℕ} (hc : c ∉ L v) :
    G.colFix L v c = 0 := by
  rw [colFix, card_eq_zero, eq_empty_iff_forall_notMem]
  intro f hf
  rw [Finset.mem_filter, mem_colorings] at hf
  exact hc (hf.2 ▸ hf.1.1 v)

/-- Splitting the colorings according to the color received by a fixed vertex `v`. -/
theorem sum_colFix (L : ListAssignment V) (v : V) :
    G.col L = ∑ c ∈ L v, G.colFix L v c :=
  Finset.card_eq_sum_card_fiberwise (fun _ hf => mem_list_of_mem_colorings hf v)

end SimpleGraph
