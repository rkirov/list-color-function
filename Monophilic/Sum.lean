/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Basic
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# List colorings of a disjoint union

The number of list colorings is multiplicative over disjoint unions. Kirov–Naimi use this
implicitly throughout (it is the reason "a graph is `n`-monophilic iff each of its connected
components is", stated without proof on p. 1), and explicitly in the proof of Lemma 2, where a
graph is cut along a bridge into two sides.

## Main results

* `SimpleGraph.col_sum` : `col(G ⊔ H, M) = col(G, M∘inl) * col(H, M∘inr)`
* `SimpleGraph.colConst_sum` : the same for constant list assignments
* `SimpleGraph.Monophilic.sum` : a disjoint union of `n`-monophilic graphs is `n`-monophilic
-/

open Finset

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]

instance : DecidableRel (G ⊕g H).Adj := fun a b =>
  match a, b with
  | .inl x, .inl y => inferInstanceAs (Decidable (G.Adj x y))
  | .inr x, .inr y => inferInstanceAs (Decidable (H.Adj x y))
  | .inl _, .inr _ => inferInstanceAs (Decidable ((false : Bool) = true))
  | .inr _, .inl _ => inferInstanceAs (Decidable ((false : Bool) = true))

/-- **Colorings multiply over a disjoint union.** -/
theorem col_sum (M : ListAssignment (V ⊕ W)) :
    (G ⊕g H).col M = G.col (M ∘ Sum.inl) * H.col (M ∘ Sum.inr) := by
  rw [col, col, col, ← Finset.card_product]
  refine Finset.card_nbij'
    (fun f => (f ∘ Sum.inl, f ∘ Sum.inr))
    (fun p => Sum.elim p.1 p.2) ?_ ?_ ?_ ?_
  · -- forward
    intro f hf
    simp only [Finset.mem_coe, mem_colorings] at hf
    simp only [Finset.mem_coe, Finset.mem_product, mem_colorings]
    exact ⟨⟨fun v => hf.1 (.inl v), fun a b hab => hf.2 (by simpa using hab)⟩,
           ⟨fun w => hf.1 (.inr w), fun a b hab => hf.2 (by simpa using hab)⟩⟩
  · -- backward
    rintro ⟨g, h⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, mem_colorings] at hp
    simp only [Finset.mem_coe, mem_colorings]
    refine ⟨?_, ?_⟩
    · rintro (v | w)
      · exact hp.1.1 v
      · exact hp.2.1 w
    · rintro (a | a) (b | b) hab
      · exact hp.1.2 (by simpa using hab)
      · exact absurd hab (by simp [SimpleGraph.sum])
      · exact absurd hab (by simp [SimpleGraph.sum])
      · exact hp.2.2 (by simpa using hab)
  · intro f _; funext x; cases x <;> rfl
  · rintro ⟨g, h⟩ _; rfl

theorem colConst_sum (n : ℕ) :
    (G ⊕g H).colConst n = G.colConst n * H.colConst n := by
  rw [colConst, colConst, colConst, col_sum]
  rfl

/-- A disjoint union of `n`-monophilic graphs is `n`-monophilic. -/
theorem Monophilic.sum {n : ℕ} (hG : G.Monophilic n) (hH : H.Monophilic n) :
    (G ⊕g H).Monophilic n := by
  intro M hM
  rw [colConst_sum, col_sum]
  exact Nat.mul_le_mul (hG _ fun v => hM (.inl v)) (hH _ fun w => hM (.inr w))

end SimpleGraph
