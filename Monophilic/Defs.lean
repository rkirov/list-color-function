/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Pi

/-!
# List colorings and `n`-monophilic graphs

Core definitions for the formalization of Kirov–Naimi, *List coloring and `n`-monophilic graphs*
(arXiv:1004.5183).

Given a graph `G` and a **list assignment** `L : V → Finset ℕ`, a *coloring of `G` from `L`* is a
function `f : V → ℕ` with `f v ∈ L v` for every vertex and `f v ≠ f w` whenever `v` and `w` are
adjacent. We write `col G L` for the number of such colorings, and `colConst G n` for the special
case where every vertex receives the same list `{0, …, n-1}` (the paper's `col(G, n)`).

`G` is **`n`-monophilic** when `col(G, n) ≤ col(G, L)` for every `n`-list assignment `L`: the count
is minimized by giving every vertex the *same* list.

## Design notes

Colorings are counted as a `Finset (V → ℕ)` carved out of `Fintype.piFinset L`, rather than via
Mathlib's bundled `G.Coloring α = G →g completeGraph α`. Mathlib provides no `Fintype` instance for
the bundled hom type, and the list constraint `f v ∈ L v` is definitional for the pi-finset. The
bundled type is used only to connect to `Colorable` / `chromaticNumber` (see `Monophilic.Basic`;
`Monophilic.Bridge` is about *graph* bridges, a different thing).

## Main definitions

* `SimpleGraph.colorings G L` : the finset of proper colorings of `G` from `L`
* `SimpleGraph.col G L` : `col(G, L)`, the number of such colorings
* `SimpleGraph.colConst G n` : `col(G, n)`, colorings from the constant list `Finset.range n`
* `SimpleGraph.IsNListAssignment L n` : every list of `L` has exactly `n` colors
* `SimpleGraph.Monophilic G n` : `G` is `n`-monophilic
-/

open Finset

namespace SimpleGraph

variable {V : Type*}

/-- A **list assignment** for a graph on `V` gives each vertex a finite set of allowed colors.
Colors are natural numbers, following the paper's `L : V → 𝒫(ℕ)`. -/
abbrev ListAssignment (V : Type*) : Type _ := V → Finset ℕ

/-- An **`n`-list assignment** gives every vertex a list of exactly `n` colors. -/
def IsNListAssignment (L : ListAssignment V) (n : ℕ) : Prop := ∀ v, (L v).card = n

/-- The constant list assignment sending every vertex to `{0, 1, …, n-1}`; the paper's `[n]`. -/
def constList (V : Type*) (n : ℕ) : ListAssignment V := fun _ => range n

@[simp] lemma constList_apply (n : ℕ) (v : V) : constList V n v = range n := rfl

lemma isNListAssignment_constList (n : ℕ) : IsNListAssignment (constList V n) n :=
  fun _ => card_range n

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `f` is a proper coloring of `G`: adjacent vertices get distinct colors. -/
def IsProperColoring (f : V → ℕ) : Prop := ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w

instance (f : V → ℕ) : Decidable (G.IsProperColoring f) := by
  unfold IsProperColoring; infer_instance

/-- The finset of proper colorings of `G` drawn from the lists `L`. -/
def colorings (L : ListAssignment V) : Finset (V → ℕ) :=
  (Fintype.piFinset L).filter G.IsProperColoring

/-- `col(G, L)`: the number of proper colorings of `G` from the list assignment `L`. -/
def col (L : ListAssignment V) : ℕ := (G.colorings L).card

/-- `col(G, n)`: the number of proper colorings of `G` from the constant list `{0, …, n-1}`. -/
def colConst (n : ℕ) : ℕ := G.col (constList V n)

/-- `G` is **`n`-monophilic** when the number of list colorings is minimized by the constant
list assignment, among all assignments of lists of size `n`. -/
def Monophilic (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → G.colConst n ≤ G.col L

variable {G}

@[simp] lemma mem_colorings {L : ListAssignment V} {f : V → ℕ} :
    f ∈ G.colorings L ↔ (∀ v, f v ∈ L v) ∧ G.IsProperColoring f := by
  simp [colorings, Fintype.mem_piFinset]

lemma mem_colorings_iff {L : ListAssignment V} {f : V → ℕ} :
    f ∈ G.colorings L ↔ (∀ v, f v ∈ L v) ∧ ∀ v w, G.Adj v w → f v ≠ f w :=
  mem_colorings

/-- Membership of the color list, for a coloring drawn from `L`. -/
lemma mem_list_of_mem_colorings {L : ListAssignment V} {f : V → ℕ}
    (hf : f ∈ G.colorings L) (v : V) : f v ∈ L v := (mem_colorings.mp hf).1 v

lemma isProperColoring_of_mem_colorings {L : ListAssignment V} {f : V → ℕ}
    (hf : f ∈ G.colorings L) : G.IsProperColoring f := (mem_colorings.mp hf).2

/-! ### Monotonicity in the lists -/

/-- Enlarging every list can only increase the number of colorings. -/
theorem colorings_subset_colorings {L L' : ListAssignment V} (h : ∀ v, L v ⊆ L' v) :
    G.colorings L ⊆ G.colorings L' := by
  intro f hf
  rw [mem_colorings] at hf ⊢
  exact ⟨fun v => h v (hf.1 v), hf.2⟩

/-- `col` is monotone in the list assignment. This is the easy half of the paper's Lemma 4. -/
theorem col_le_col_of_subset {L L' : ListAssignment V} (h : ∀ v, L v ⊆ L' v) :
    G.col L ≤ G.col L' :=
  card_le_card (colorings_subset_colorings h)

/-! ### Positivity -/

lemma col_pos_iff {L : ListAssignment V} : 0 < G.col L ↔ ∃ f, f ∈ G.colorings L := by
  rw [col, card_pos]
  exact ⟨fun ⟨f, hf⟩ => ⟨f, hf⟩, fun ⟨f, hf⟩ => ⟨f, hf⟩⟩

lemma col_eq_zero_iff {L : ListAssignment V} :
    G.col L = 0 ↔ ∀ f, (∀ v, f v ∈ L v) → ¬ G.IsProperColoring f := by
  rw [col, card_eq_zero, eq_empty_iff_forall_notMem]
  simp only [mem_colorings, not_and]

end SimpleGraph
