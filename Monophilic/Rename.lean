/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Defs
import Mathlib.Data.Finset.Sort

/-!
# Renaming colors

`col G L` depends on the list assignment `L` only up to renaming of the colors. This is used
constantly in Kirov–Naimi, which freely says things like "without loss of generality
`L(x) = {1,2}`", and it is what makes the constant list `{0, …, n-1}` a legitimate stand-in for an
arbitrary `n`-element color set.

## Main results

* `SimpleGraph.col_image_of_injOn` : applying a function injective on the available colors to every
  list leaves `col` unchanged.
* `SimpleGraph.col_const_eq_colConst` : any constant list assignment by an `n`-element set of colors
  gives the paper's `col(G, n)`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
/-- The colors used by a coloring drawn from `L` lie in the union of the lists. -/
private lemma mem_iUnion_coe {L : ListAssignment V} {c : ℕ} {v : V} (h : c ∈ L v) :
    c ∈ ⋃ w, (L w : Set ℕ) := Set.mem_iUnion.mpr ⟨v, h⟩

/-- Renaming the colors by a function injective on the colors actually available does not change
the number of list colorings. -/
theorem col_image_of_injOn {L : ListAssignment V} {e : ℕ → ℕ}
    (he : Set.InjOn e (⋃ v, (L v : Set ℕ))) :
    G.col (fun v => (L v).image e) = G.col L := by
  symm
  refine Finset.card_bij (fun f _ => e ∘ f) ?_ ?_ ?_
  · -- the renamed coloring is a coloring from the renamed lists
    intro f hf
    rw [mem_colorings] at hf ⊢
    refine ⟨fun v => Finset.mem_image_of_mem e (hf.1 v), ?_⟩
    intro v w hvw hcon
    exact hf.2 hvw (he (mem_iUnion_coe (hf.1 v)) (mem_iUnion_coe (hf.1 w)) hcon)
  · -- injectivity
    intro f₁ h₁ f₂ h₂ heq
    rw [mem_colorings] at h₁ h₂
    funext v
    exact he (mem_iUnion_coe (h₁.1 v)) (mem_iUnion_coe (h₂.1 v)) (congrFun heq v)
  · -- surjectivity
    intro g hg
    rw [mem_colorings] at hg
    choose f hf₁ hf₂ using fun v => Finset.mem_image.mp (hg.1 v)
    refine ⟨f, ?_, funext hf₂⟩
    rw [mem_colorings]
    refine ⟨hf₁, ?_⟩
    intro v w hvw hcon
    exact hg.2 hvw (by rw [← hf₂ v, ← hf₂ w, hcon])

/-- Colorings from a constant list assignment are counted by `col(G, n)`, for any `n`-element set
of colors. -/
theorem col_const_eq_colConst {s : Finset ℕ} {n : ℕ} (hs : s.card = n) :
    G.col (fun _ => s) = G.colConst n := by
  classical
  refine Finset.card_bij'
    (fun f hf v => ((s.orderIsoOfFin hs).symm ⟨f v, (mem_colorings.mp hf).1 v⟩ : Fin n).val)
    (fun g hg v => (((s.orderIsoOfFin hs)
      ⟨g v, Finset.mem_range.mp ((mem_colorings.mp hg).1 v)⟩ : s) : ℕ))
    ?_ ?_ ?_ ?_
  · -- lands in colorings from `range n`
    intro f hf
    rw [mem_colorings]
    refine ⟨fun v => Finset.mem_range.mpr (Fin.is_lt _), ?_⟩
    intro v w hvw hcon
    refine (mem_colorings.mp hf).2 hvw ?_
    have := Fin.val_injective hcon
    simpa using congrArg (fun x => ((s.orderIsoOfFin hs) x : ℕ)) this
  · -- lands in colorings from `s`
    intro g hg
    rw [mem_colorings]
    refine ⟨fun v => ((s.orderIsoOfFin hs) _).2, ?_⟩
    intro v w hvw hcon
    refine (mem_colorings.mp hg).2 hvw ?_
    have : ((s.orderIsoOfFin hs) ⟨g v, _⟩ : s) = (s.orderIsoOfFin hs) ⟨g w, _⟩ :=
      Subtype.ext hcon
    simpa using congrArg (fun x => (x : Fin n).val) ((s.orderIsoOfFin hs).injective this)
  · intro f hf; funext v; simp
  · intro g hg; funext v
    rw [Subtype.coe_eta, OrderIso.symm_apply_apply]

end SimpleGraph
