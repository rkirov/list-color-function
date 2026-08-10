/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The chromatic polynomial of a finite simple graph

Mathlib has no chromatic polynomial, and it has no edge contraction either, so the usual
deletion–contraction recursion is not available to us.  We therefore take the **Whitney rank
generating (subset) expansion** as the *definition*:

`P(G, X) = ∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`,

where `c(S)` is the number of connected components of the spanning subgraph `(V, S)`.  This has
three advantages here: it visibly produces a polynomial with integer coefficients, it needs nothing
beyond `SimpleGraph.fromEdgeSet` and `SimpleGraph.ConnectedComponent` (both already in Mathlib), and
its correctness proof is a single inclusion–exclusion computation over the edge set rather than an
induction on the number of edges.

The link back to `ListColoring.Defs` is `eval_chromaticPolynomial`: evaluating at a natural number
`n` gives `col(G, n)`, the number of proper colorings of `G` from the constant list `{0, …, n-1}`.

## Main results

* `SimpleGraph.compCount` : `c(S)`, the number of components of the spanning subgraph `(V, S)`
* `SimpleGraph.chromaticPolynomial` : the Whitney expansion, as a `Polynomial ℤ`
* `SimpleGraph.whitneySum` : the same sum with an integer in place of `X`; unlike the polynomial it
  is computable, so it is what the numerical checks at the bottom of the file exercise
* `SimpleGraph.card_filter_constOnEdges` : there are exactly `n ^ c(S)` functions `V → {0, …, n-1}`
  that are constant on every edge of `S`
* `SimpleGraph.eval_chromaticPolynomial` : `P(G, n) = col(G, n)`
* `SimpleGraph.chromaticPolynomial_bot` : `P(⊥, X) = X ^ |V|`
-/

open Finset

namespace SimpleGraph

/-! ### Functions constant along the edges of a graph

Nothing in this section needs finiteness, so it is stated for an arbitrary vertex type. -/

section General

variable {V : Type*}

/-- A function that is constant along every edge of a graph is constant on reachability classes. -/
theorem eq_of_reachable_of_adj_imp_eq {H : SimpleGraph V} {f : V → ℕ}
    (hf : ∀ v w, H.Adj v w → f v = f w) {v w : V} (h : H.Reachable v w) : f v = f w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

/-- In a graph with no edges, reachability is equality. -/
theorem eq_of_reachable_of_no_adj {H : SimpleGraph V} (h : ∀ v w, ¬ H.Adj v w)
    {v w : V} (hr : H.Reachable v w) : v = w := by
  obtain ⟨p⟩ := hr
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (h _ _)

/-- `f` takes the same value at the two ends of the edge `e`.  For a loop `s(v, v)` this holds
vacuously, matching the fact that `fromEdgeSet` discards loops. -/
def ConstOnEdge (f : V → ℕ) (e : Sym2 V) : Prop := (Sym2.map f e).IsDiag

instance (f : V → ℕ) : DecidablePred (ConstOnEdge f) :=
  fun _ => inferInstanceAs (Decidable (Sym2.IsDiag _))

@[simp] lemma constOnEdge_mk (f : V → ℕ) (v w : V) : ConstOnEdge f s(v, w) ↔ f v = f w := by
  simp [ConstOnEdge]

/-- Being constant on every edge of `S` is the same as being constant along every adjacency of the
spanning subgraph `fromEdgeSet S`.  The two differ only on loops of `S`, which constrain nothing on
either side. -/
theorem forall_constOnEdge_iff {S : Finset (Sym2 V)} {f : V → ℕ} :
    (∀ e ∈ S, ConstOnEdge f e) ↔
      ∀ v w, (fromEdgeSet (S : Set (Sym2 V))).Adj v w → f v = f w := by
  constructor
  · intro h v w hvw
    rw [fromEdgeSet_adj] at hvw
    exact (constOnEdge_mk f v w).mp (h _ hvw.1)
  · intro h e he
    induction e using Sym2.ind with
    | _ v w =>
      rw [constOnEdge_mk]
      by_cases hvw : v = w
      · rw [hvw]
      · exact h v w (by rw [fromEdgeSet_adj]; exact ⟨he, hvw⟩)

/-- Summing an indicator counts the members of the corresponding filter. -/
theorem sum_ite_one_zero {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∑ i ∈ s, if p i then (1 : ℤ) else 0) = (#{i ∈ s | p i} : ℤ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Expanding a product of `1 - g e` over all subsets of `s`: the inclusion–exclusion identity
behind the Whitney expansion. -/
theorem prod_one_sub_eq_sum_powerset {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℤ) :
    ∏ e ∈ s, (1 - g e) = ∑ t ∈ s.powerset, (-1) ^ #t * ∏ e ∈ t, g e := by
  have h : ∀ e : ι, (1 : ℤ) - g e = -g e + 1 := fun e => by ring
  simp_rw [h]
  rw [Finset.prod_add]
  exact Finset.sum_congr rfl fun t _ => by rw [Finset.prod_neg, Finset.prod_const_one, mul_one]

end General

/-! ### Counting components of a spanning subgraph -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency in `fromEdgeSet S` is decidable when `S` comes from a `Finset` of edges.  This is
what supplies the `Fintype` structure on the connected components, and it also makes `compCount`
(hence the whole Whitney sum) computable. -/
instance decidableRelFromEdgeSetCoe (S : Finset (Sym2 V)) :
    DecidableRel (fromEdgeSet (S : Set (Sym2 V))).Adj :=
  fun _ _ => decidable_of_iff' _ (fromEdgeSet_adj _)

/-- `c(S)`: the number of connected components of the spanning subgraph of `V` whose edges are
exactly the non-loop elements of `S`.  Isolated vertices each count as a component. -/
def compCount (S : Finset (Sym2 V)) : ℕ :=
  Fintype.card (fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent

/-- With no edges, every vertex is its own component. -/
theorem compCount_empty : compCount (∅ : Finset (Sym2 V)) = Fintype.card V := by
  set H : SimpleGraph V := fromEdgeSet ((∅ : Finset (Sym2 V)) : Set (Sym2 V)) with hH
  have hadj : ∀ v w, ¬ H.Adj v w := by
    intro v w hvw
    rw [hH, fromEdgeSet_adj] at hvw
    simpa using hvw.1
  exact (Fintype.card_of_bijective (f := H.connectedComponentMk)
    ⟨fun v w h => eq_of_reachable_of_no_adj hadj (ConnectedComponent.exact h),
      fun c => c.ind fun v => ⟨v, rfl⟩⟩).symm

/-- **The key counting lemma.**  The functions `V → {0, …, n-1}` that are constant on every edge of
`S` are exactly the functions that factor through the connected components of `(V, S)`, so there
are `n ^ c(S)` of them. -/
theorem card_filter_constOnEdges (S : Finset (Sym2 V)) (n : ℕ) :
    #{f ∈ Fintype.piFinset fun _ : V => range n | ∀ e ∈ S, ConstOnEdge f e} = n ^ compCount S := by
  classical
  set H : SimpleGraph V := fromEdgeSet (S : Set (Sym2 V)) with hH
  have key : #(Fintype.piFinset fun _ : H.ConnectedComponent => range n) =
      #{f ∈ Fintype.piFinset fun _ : V => range n | ∀ e ∈ S, ConstOnEdge f e} := by
    refine Finset.card_bij (fun g _ v => g (H.connectedComponentMk v)) ?_ ?_ ?_
    · intro g hg
      rw [Fintype.mem_piFinset] at hg
      rw [mem_filter, Fintype.mem_piFinset]
      exact ⟨fun _ => hg _, forall_constOnEdge_iff.mpr fun v w hvw => by
        rw [ConnectedComponent.connectedComponentMk_eq_of_adj hvw]⟩
    · intro g₁ _ g₂ _ h
      funext c
      induction c using ConnectedComponent.ind with
      | _ v => exact congrFun h v
    · intro f hf
      rw [mem_filter, Fintype.mem_piFinset] at hf
      have hconst : ∀ v w, H.Adj v w → f v = f w := forall_constOnEdge_iff.mp hf.2
      refine ⟨ConnectedComponent.lift f fun v w p _ => eq_of_reachable_of_adj_imp_eq hconst ⟨p⟩,
        ?_, rfl⟩
      rw [Fintype.mem_piFinset]
      intro c
      induction c using ConnectedComponent.ind with
      | _ v => exact hf.1 v
  rw [← key, Fintype.card_piFinset, Finset.prod_const, card_range, Finset.card_univ, compCount]

/-- The `ℤ`-valued form of `card_filter_constOnEdges` used in the inclusion–exclusion computation:
summing, over all `f : V → {0, …, n-1}`, the product over `e ∈ S` of the indicator that `f` is
constant on `e`, gives `n ^ c(S)`. -/
theorem sum_prod_constOnEdge_indicator (S : Finset (Sym2 V)) (n : ℕ) :
    (∑ f ∈ Fintype.piFinset fun _ : V => range n,
        ∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0) = (n : ℤ) ^ compCount S := by
  have key : ∀ f : V → ℕ, (∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0)
      = if ∀ e ∈ S, ConstOnEdge f e then (1 : ℤ) else 0 := by
    intro f
    by_cases h : ∀ e ∈ S, ConstOnEdge f e
    · rw [if_pos h]
      exact Finset.prod_eq_one fun e he => if_pos (h e he)
    · rw [if_neg h]
      push Not at h
      obtain ⟨e, he, hne⟩ := h
      exact Finset.prod_eq_zero he (if_neg hne)
  simp_rw [key]
  rw [sum_ite_one_zero, card_filter_constOnEdges S n, Nat.cast_pow]

/-! ### The polynomial -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **chromatic polynomial** of `G`, defined by the Whitney subset expansion
`∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`.  See `SimpleGraph.eval_chromaticPolynomial` for the fact that
this really counts proper colorings. -/
noncomputable def chromaticPolynomial : Polynomial ℤ :=
  ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * Polynomial.X ^ compCount S

/-- The Whitney sum evaluated at an integer.  Unlike `chromaticPolynomial` this is computable, so
it can be used for numerical checks. -/
def whitneySum (x : ℤ) : ℤ :=
  ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * x ^ compCount S

/-- Evaluating the chromatic polynomial at `x` is the same as forming the Whitney sum with `x` in
place of `X`. -/
@[simp] theorem eval_chromaticPolynomial_eq_whitneySum (x : ℤ) :
    (G.chromaticPolynomial).eval x = G.whitneySum x := by
  rw [chromaticPolynomial, whitneySum, Polynomial.eval_finsetSum]
  simp

omit [DecidableEq V] in
/-- The product over the edges of `1 -` (the indicator that the two ends receive the same color) is
the indicator that the coloring is proper. -/
theorem prod_one_sub_indicator (f : V → ℕ) :
    (∏ e ∈ G.edgeFinset, (1 - if ConstOnEdge f e then (1 : ℤ) else 0)) =
      if G.IsProperColoring f then 1 else 0 := by
  by_cases hf : G.IsProperColoring f
  · rw [if_pos hf]
    refine Finset.prod_eq_one fun e he => ?_
    rw [mem_edgeFinset] at he
    revert he
    induction e using Sym2.ind with
    | _ v w =>
      intro he
      rw [mem_edgeSet] at he
      rw [if_neg ((constOnEdge_mk f v w).not.mpr (hf he)), sub_zero]
  · rw [if_neg hf]
    have hex : ∃ v w, G.Adj v w ∧ f v = f w := by
      by_contra hcon
      push Not at hcon
      exact hf fun v w hvw => hcon v w hvw
    obtain ⟨v, w, hvw, heq⟩ := hex
    refine Finset.prod_eq_zero (i := s(v, w)) ?_ ?_
    · rw [mem_edgeFinset, mem_edgeSet]; exact hvw
    · rw [if_pos ((constOnEdge_mk f v w).mpr heq), sub_self]

/-- **Evaluation of the chromatic polynomial counts colorings.**  At a natural number `n`, the
Whitney expansion returns `col(G, n)`, the number of proper colorings of `G` drawn from
`{0, …, n-1}`. -/
theorem eval_chromaticPolynomial (n : ℕ) :
    (G.chromaticPolynomial).eval (n : ℤ) = (G.colConst n : ℤ) := by
  rw [eval_chromaticPolynomial_eq_whitneySum, whitneySum, colConst, col, colorings]
  have hlist : Fintype.piFinset (constList V n) = Fintype.piFinset fun _ : V => range n := rfl
  rw [hlist, ← sum_ite_one_zero]
  calc ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * (n : ℤ) ^ compCount S
      = ∑ S ∈ G.edgeFinset.powerset, ∑ f ∈ Fintype.piFinset fun _ : V => range n,
          (-1) ^ #S * ∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.mul_sum, sum_prod_constOnEdge_indicator S n]
    _ = ∑ f ∈ Fintype.piFinset fun _ : V => range n, ∑ S ∈ G.edgeFinset.powerset,
          (-1) ^ #S * ∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0 := Finset.sum_comm
    _ = ∑ f ∈ Fintype.piFinset fun _ : V => range n,
          if G.IsProperColoring f then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← prod_one_sub_eq_sum_powerset, prod_one_sub_indicator]

/-! ### Special cases -/

/-- If `G` has no edges the Whitney sum collapses to its single term `X ^ |V|`. -/
theorem chromaticPolynomial_eq_of_edgeFinset_eq_empty (h : G.edgeFinset = ∅) :
    chromaticPolynomial G = Polynomial.X ^ Fintype.card V := by
  rw [chromaticPolynomial, h, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty,
    pow_zero, one_mul, compCount_empty]

/-- The chromatic polynomial of the edgeless graph is `X ^ |V|`: the Whitney sum has a single
term, and every vertex is its own component. -/
theorem chromaticPolynomial_bot [DecidableRel (⊥ : SimpleGraph V).Adj] :
    chromaticPolynomial (⊥ : SimpleGraph V) = Polynomial.X ^ Fintype.card V :=
  chromaticPolynomial_eq_of_edgeFinset_eq_empty _ (by ext e; simp)

/-- The chromatic polynomial of the edgeless graph has degree `|V|`, as every chromatic polynomial
should. -/
theorem natDegree_chromaticPolynomial_bot [DecidableRel (⊥ : SimpleGraph V).Adj] :
    (chromaticPolynomial (⊥ : SimpleGraph V)).natDegree = Fintype.card V := by
  rw [chromaticPolynomial_bot, Polynomial.natDegree_X_pow]

end SimpleGraph

/-! ### Numerical checks

`chromaticPolynomial` is `noncomputable` (as is `Polynomial.eval`), so the checks below are run on
`whitneySum`, which is the same sum with `Polynomial.X` replaced by an integer; the two are linked
by `eval_chromaticPolynomial_eq_whitneySum`.  The triangle `⊤ : SimpleGraph (Fin 3)` has
`P(X) = X(X-1)(X-2)`, and the single edge `⊤ : SimpleGraph (Fin 2)` has `P(X) = X(X-1)`. -/

section Checks

open SimpleGraph

-- triangle: `P(3) = 3·2·1 = 6`, `P(4) = 4·3·2 = 24`
#guard (⊤ : SimpleGraph (Fin 3)).colConst 3 = 6
#guard (⊤ : SimpleGraph (Fin 3)).whitneySum 3 = 6
#guard (⊤ : SimpleGraph (Fin 3)).colConst 4 = 24
#guard (⊤ : SimpleGraph (Fin 3)).whitneySum 4 = 24
-- single edge: `P(3) = 3·2 = 6`
#guard (⊤ : SimpleGraph (Fin 2)).colConst 3 = 6
#guard (⊤ : SimpleGraph (Fin 2)).whitneySum 3 = 6
-- edgeless graph on three vertices: `P(3) = 3³ = 27`
#guard (⊥ : SimpleGraph (Fin 3)).colConst 3 = 27
#guard (⊥ : SimpleGraph (Fin 3)).whitneySum 3 = 27
-- `K₄`: `P(4) = 4·3·2·1 = 24`, `P(3) = 0`
#guard (⊤ : SimpleGraph (Fin 4)).colConst 4 = 24
#guard (⊤ : SimpleGraph (Fin 4)).whitneySum 4 = 24
#guard (⊤ : SimpleGraph (Fin 4)).whitneySum 3 = 0
-- a path on three vertices (one vertex of degree two): `P(X) = X(X-1)²`, so `P(3) = 12`
#guard (SimpleGraph.fromRel fun a b : Fin 3 => a.val + 1 = b.val).colConst 3 = 12
#guard (SimpleGraph.fromRel fun a b : Fin 3 => a.val + 1 = b.val).whitneySum 3 = 12

end Checks
