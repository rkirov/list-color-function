/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Defs

/-!
# Invariance under graph isomorphism

Nothing in the theory of list colorings sees the names of the vertices: an isomorphism
`e : G ≃g G'` matches the colorings of `G'` from a list assignment `M` one for one with the
colorings of `G` from the transported assignment `M ∘ e`. Consequently `col`, `colConst` and
`ECCAt` are isomorphism invariants.

This is pure transport, but it is what lets an argument that builds a graph up structurally (as in
`ListColoring.Cone`, where a new vertex is added as an `Option`) be applied to a concretely indexed
graph such as `⊤ : SimpleGraph (Fin m)`.

## Main results

* `SimpleGraph.col_comp_iso` : `col(G, M ∘ e) = col(G', M)` for `e : G ≃g G'`
* `SimpleGraph.colConst_iso` : `col(G, n) = col(G', n)`
* `SimpleGraph.ecc_iso` : `G` is enumeratively chromatic-choosable at `n` iff `G'` is
-/

open Finset

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]

/-! ### Transporting a single coloring -/

/-- Precomposing with an isomorphism `e : G ≃g G'` turns a coloring of `G'` from `M` into a
coloring of `G` from the transported list assignment `M ∘ e`. -/
theorem mem_colorings_comp_iso (e : G ≃g G') {M : ListAssignment W} {g : W → ℕ}
    (hg : g ∈ G'.colorings M) : g ∘ e ∈ G.colorings (M ∘ e) := by
  rw [mem_colorings] at hg ⊢
  refine ⟨fun v => hg.1 (e v), ?_⟩
  intro v w hvw
  exact hg.2 (e.map_rel_iff.mpr hvw)

/-! ### Invariance of the counts -/

/-- **`col` is an isomorphism invariant.** For `e : G ≃g G'` and a list assignment `M` on the
vertices of `G'`, the colorings of `G` from `M ∘ e` are exactly the colorings of `G'` from `M`,
read through `e`.

Applying this to `e.symm : G' ≃g G` gives the mirror statement `col(G', L ∘ e.symm) = col(G, L)`. -/
theorem col_comp_iso (e : G ≃g G') (M : ListAssignment W) : G.col (M ∘ e) = G'.col M := by
  refine Finset.card_nbij' (fun f => f ∘ e.symm) (fun g => g ∘ e) ?_ ?_ ?_ ?_
  · -- pushing a coloring of `G` forward along `e.symm`
    intro f hf
    rw [Finset.mem_coe, mem_colorings] at hf
    rw [Finset.mem_coe, mem_colorings]
    refine ⟨fun w => ?_, ?_⟩
    · simpa using hf.1 (e.symm w)
    · intro w₁ w₂ hw
      exact hf.2 (e.symm.map_rel_iff.mpr hw)
  · -- pulling a coloring of `G'` back along `e`
    intro g hg
    exact Finset.mem_coe.mpr (mem_colorings_comp_iso e (Finset.mem_coe.mp hg))
  · intro f _
    funext v
    simp
  · intro g _
    funext w
    simp

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [DecidableRel G.Adj]
  [DecidableRel G'.Adj] in
/-- Transporting the constant list assignment along an isomorphism gives the constant list
assignment. -/
@[simp] theorem constList_comp_iso (e : G ≃g G') (n : ℕ) :
    constList W n ∘ e = constList V n := rfl

/-- **`colConst` is an isomorphism invariant.** -/
theorem colConst_iso (e : G ≃g G') (n : ℕ) : G.colConst n = G'.colConst n := by
  rw [colConst, colConst, ← constList_comp_iso e n, col_comp_iso]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [DecidableRel G.Adj]
  [DecidableRel G'.Adj] in
/-- Transporting an `n`-list assignment along an isomorphism gives an `n`-list assignment. -/
theorem isNListAssignment_comp_iso (e : G ≃g G') {M : ListAssignment W} {n : ℕ}
    (hM : IsNListAssignment M n) : IsNListAssignment (M ∘ e) n := fun v => hM (e v)

/-! ### Invariance of enumerative chromatic-choosability -/

/-- **Enumerative chromatic-choosability is an isomorphism invariant.** -/
theorem ecc_iso (e : G ≃g G') (n : ℕ) : G.ECCAt n ↔ G'.ECCAt n := by
  constructor
  · intro h M hM
    rw [← colConst_iso e, ← col_comp_iso e M]
    exact h _ (isNListAssignment_comp_iso e hM)
  · intro h L hL
    rw [colConst_iso e, ← col_comp_iso e.symm L]
    exact h _ (isNListAssignment_comp_iso e.symm hL)

end SimpleGraph
