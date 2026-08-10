/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Pi

/-!
# List colorings and graphs that are enumeratively chromatic-choosable at `n`

Core definitions for the formalization of Kirov–Naimi, *List coloring and `n`-monophilic graphs*
(arXiv:1004.5183).

Given a graph `G` and a **list assignment** `L : V → Finset ℕ`, a *coloring of `G` from `L`* is a
function `f : V → ℕ` with `f v ∈ L v` for every vertex and `f v ≠ f w` whenever `v` and `w` are
adjacent. We write `col G L` for the number of such colorings, and `colConst G n` for the special
case where every vertex receives the same list `{0, …, n-1}` (the paper's `col(G, n)`).

`G` is **enumeratively chromatic-choosable at `n`** when `col(G, n) ≤ col(G, L)` for every `n`-list
assignment `L`: the count is minimized by giving every vertex the *same* list. `G` is
**enumeratively chromatic-choosable** when that holds at every `n`.

## The name

Kirov and Naimi call the pointwise property "`n`-monophilic"; that is the historical name, and it is
the one the paper being formalized uses. The name the literature settled on is *enumeratively
chromatic-choosable*, first formally defined in Kaul et al., *Bounding the list color function
threshold from above*, Involve **16** (2023) 849–882, and used in that form by Allred–Mudrock
(arXiv:2505.05662) and Chi et al. (arXiv:2605.10861). It is built on Ohba's
*chromatic-choosable*, `χ(G) = χ_ℓ(G)` — lists cost nothing at the level of the *number*. Here they
cost nothing at the level of the *count*: `P_ℓ` is the enumerative analogue of the chromatic
polynomial, so the same property is lifted from a number to a counting function
(`SimpleGraph.ecc_iff_listColorFunction_eq`). The implication runs the right way, which is what
justifies the name — see `SimpleGraph.choosable_of_ecc_of_colorable`.

Two predicates are provided, and the pointwise one is the workhorse, since Kirov–Naimi's Theorem 1
is "for every `n`" and Theorem 2 is at `n = 2`:

* `SimpleGraph.ECCAt G n` — enumeratively chromatic-choosable **at `n`**, the historical
  "`n`-monophilic";
* `SimpleGraph.ECC G` — enumeratively chromatic-choosable, i.e. `∀ n, G.ECCAt n`.

`ECCAt` at `n < χ(G)` is vacuous (`SimpleGraph.ecc_of_not_colorable`), so `ECC` agrees with the
literature's `τ(G) = χ(G)`, which quantifies only over `n ≥ χ(G)`.

## Design notes

Colorings are counted as a `Finset (V → ℕ)` carved out of `Fintype.piFinset L`, rather than via
Mathlib's bundled `G.Coloring α = G →g completeGraph α`. Mathlib provides no `Fintype` instance for
the bundled hom type, and the list constraint `f v ∈ L v` is definitional for the pi-finset. The
bundled type is used only to connect to `Colorable` / `chromaticNumber` (see `ListColoring.Basic`;
`ListColoring.Bridge` is about *graph* bridges, a different thing).

## Main definitions

* `SimpleGraph.colorings G L` : the finset of proper colorings of `G` from `L`
* `SimpleGraph.col G L` : `col(G, L)`, the number of such colorings
* `SimpleGraph.colConst G n` : `col(G, n)`, colorings from the constant list `Finset.range n`
* `SimpleGraph.IsNListAssignment L n` : every list of `L` has exactly `n` colors
* `SimpleGraph.ECCAt G n` : `G` is enumeratively chromatic-choosable at `n`
  (Kirov–Naimi's `n`-monophilic)
* `SimpleGraph.ECC G` : `G` is enumeratively chromatic-choosable, i.e. `∀ n, G.ECCAt n`
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

/-- `G` is **enumeratively chromatic-choosable at `n`** when the number of list colorings is
minimized by the constant list assignment, among all assignments of lists of size `n`.

This is Kirov–Naimi's "`n`-monophilic", under the name the literature settled on; see the note on
the name in the module docstring. -/
def ECCAt (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → G.colConst n ≤ G.col L

/-- `G` is **enumeratively chromatic-choosable** when it is enumeratively chromatic-choosable at
every `n`: no list assignment ever admits fewer colorings than the constant one of the same size.

Kirov–Naimi have no name for this; they work with the pointwise `n`-monophilic. Quantifying over
*all* `n` rather than over `n ≥ χ(G)` costs nothing, because below `χ(G)` the pointwise property is
vacuous (`SimpleGraph.ecc_of_not_colorable`); see `SimpleGraph.ecc_iff_forall_two_le` for the
sharper reformulation that is usually the one to prove. -/
def ECC : Prop := ∀ n, G.ECCAt n

variable {G}

/-- An enumeratively chromatic-choosable graph is enumeratively chromatic-choosable at each `n`.
This is `rfl`, and exists so that `h.eccAt n` is available by dot notation. -/
theorem ECC.eccAt (h : G.ECC) (n : ℕ) : G.ECCAt n := h n

theorem ecc_iff_forall : G.ECC ↔ ∀ n, G.ECCAt n := Iff.rfl

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
