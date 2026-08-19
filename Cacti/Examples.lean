/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Statements

/-!
# Concrete cacti: the definition is neither too weak nor too strong

`IsCactus` says that any two cycles sharing an edge have the same edge *set*.  Everything the
classification proves rests on that reading, so this file pins it down on three graphs, and then
applies the classification to one of them.

The formulation is deliberate.  A cycle is a walk, and one cycle has many walks -- different
basepoints, and both directions.  Had the definition asked for `p = q` it would be false for every
graph containing a cycle, cacti would collapse to forests, and the classification would be a
statement about trees.  Edge-set equality is how one says "the same cycle"; nothing is lost by
`toFinset`, since `IsCycle` gives `edges.Nodup`.

Three checks, in increasing order of interest:

* `K₄` is refused -- two triangles meet on the edge `01` with different edge sets;
* a triangle is accepted -- the test the naive `p = q` version fails;
* the *bowtie*, two triangles glued at a vertex, is accepted, and is not `HasAtMostOneCycle`.

The last is the one that matters: it is a cactus with two cycles, which is exactly what separates
the `IsCactus` hypothesis from the `HasAtMostOneCycle` alternative in `isCactus_ecc_iff`.  The file
ends by running the classification on it.

Nothing in the library depends on this file; it is evidence, not machinery.
-/

open SimpleGraph

namespace ListColoring.CactusExamples


/-! ## `K₄` is not a cactus: two triangles sharing the edge `01`, with different edge sets. -/
section K4
abbrev K4 : SimpleGraph (Fin 4) := ⊤

def tri012 : K4.Walk 0 0 :=                                          -- 0 → 1 → 2 → 0
  .cons (show K4.Adj 0 1 by decide) (.cons (show K4.Adj 1 2 by decide)
    (.cons (show K4.Adj 2 0 by decide) .nil))
def tri013 : K4.Walk 0 0 :=                                          -- 0 → 1 → 3 → 0
  .cons (show K4.Adj 0 1 by decide) (.cons (show K4.Adj 1 3 by decide)
    (.cons (show K4.Adj 3 0 by decide) .nil))

theorem tri012_cycle : tri012.IsCycle := by
  rw [Walk.isCycle_def]; exact ⟨⟨by decide⟩, by simp [tri012], by decide⟩
theorem tri013_cycle : tri013.IsCycle := by
  rw [Walk.isCycle_def]; exact ⟨⟨by decide⟩, by simp [tri013], by decide⟩

theorem not_isCactus_K4 : ¬ IsCactus K4 := by
  rintro ⟨-, h⟩
  have hEq := h tri012 tri013 tri012_cycle tri013_cycle s(0, 1) (by decide) (by decide)
  have : s(1, 2) ∈ tri012.edges.toFinset := by decide
  rw [hEq] at this
  revert this; decide
end K4

/-! ## A triangle is a cactus — the test a naive `p = q` version fails, since a cycle
traversed backwards is a different walk with the same edge set. -/
section C3
abbrev C3 : SimpleGraph (Fin 3) := ⊤

theorem C3_connected : C3.Connected := by
  constructor
  · intro u v
    rcases eq_or_ne u v with rfl | h
    · exact .refl _
    · exact (SimpleGraph.top_adj u v |>.mpr h).reachable

theorem C3_cycle_edges {u : Fin 3} (p : C3.Walk u u) (hp : p.IsCycle) :
    p.edges.toFinset = C3.edgeFinset := by
  refine Finset.eq_of_subset_of_card_le (fun e he => ?_) ?_
  · simpa using p.edges_subset_edgeSet (List.mem_toFinset.mp he)
  · have hcard : C3.edgeFinset.card = 3 := by
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]; decide
    rw [List.toFinset_card_of_nodup hp.edges_nodup, Walk.length_edges, hcard]
    exact hp.three_le_length

theorem isCactus_C3 : IsCactus C3 :=
  ⟨C3_connected, fun ⦃_ _⦄ p q hp hq _ _ _ => by
    rw [C3_cycle_edges p hp, C3_cycle_edges q hq]⟩
end C3

/-! ## The bowtie

The **bowtie**: two triangles sharing the vertex `0`.  `0` is joined to all of `1,2,3,4`,
plus the edges `12` and `34`.  A cactus with two cycles — the case that separates `IsCactus`
from `HasAtMostOneCycle`. -/

/-- `0` is joined to everything, plus `1-2` and `3-4`. -/
def bowRel (a b : Fin 5) : Prop := b = 0 ∨ (a = 1 ∧ b = 2) ∨ (a = 3 ∧ b = 4)

instance : DecidableRel bowRel := fun a b => by unfold bowRel; infer_instance

def bow : SimpleGraph (Fin 5) := SimpleGraph.fromRel bowRel

instance : DecidableRel bow.Adj :=
  fun a b => decidable_of_iff _ (SimpleGraph.fromRel_adj (r := bowRel) (v := a) (w := b)).symm

/-- the two triangles, as edge sets -/
def T1 : Finset (Sym2 (Fin 5)) := {s(0,1), s(1,2), s(2,0)}
def T2 : Finset (Sym2 (Fin 5)) := {s(0,3), s(3,4), s(4,0)}

/-- **Every cycle of the bowtie is one of the two triangles.**  Decided by enumerating every
closed walk of length ≤ 5 (a cycle's support tail is nodup in `Fin 5`, so it can be no longer). -/
theorem bow_cycle_edges {u : Fin 5} (p : bow.Walk u u) (hp : p.IsCycle) :
    p.edges.toFinset = T1 ∨ p.edges.toFinset = T2 := by
  have hlen : p.length ≤ 5 := by
    have h := hp.support_nodup
    have : p.support.tail.length ≤ Fintype.card (Fin 5) := List.Nodup.length_le_card h
    simpa using this
  have key : ∀ n ∈ Finset.range 6, ∀ v : Fin 5, ∀ q ∈ bow.finsetWalkLength n v v,
      q.edges.Nodup → q.support.tail.Nodup → 3 ≤ q.length →
      q.edges.toFinset = T1 ∨ q.edges.toFinset = T2 := by decide
  exact key p.length (Finset.mem_range.mpr (by omega)) u p
    (SimpleGraph.mem_finsetWalkLength_iff.mpr rfl) hp.edges_nodup hp.support_nodup
    hp.three_le_length

theorem bow_adj_zero {u : Fin 5} (h : u ≠ 0) : bow.Adj u 0 := by
  rw [bow, SimpleGraph.fromRel_adj]; exact ⟨h, Or.inl (Or.inl rfl)⟩

theorem bow_connected : bow.Connected := by
  constructor
  · intro u v
    rcases eq_or_ne u 0 with rfl | hu <;> rcases eq_or_ne v 0 with rfl | hv
    · exact .refl _
    · exact ((bow_adj_zero hv).symm).reachable
    · exact (bow_adj_zero hu).reachable
    · exact ((bow_adj_zero hu).reachable).trans ((bow_adj_zero hv).symm).reachable

/-- **The bowtie is a cactus.**  Two cycles that share an edge must be the same triangle, since
the two triangles are edge-disjoint. -/
theorem bow_isCactus : IsCactus bow := by
  have hdisj : T1 ∩ T2 = (∅ : Finset (Sym2 (Fin 5))) := by decide
  refine ⟨bow_connected, fun ⦃_ _⦄ p q hp hq e hep heq => ?_⟩
  have hpe : e ∈ p.edges.toFinset := List.mem_toFinset.mpr hep
  have hqe : e ∈ q.edges.toFinset := List.mem_toFinset.mpr heq
  rcases bow_cycle_edges p hp with h1 | h1 <;> rcases bow_cycle_edges q hq with h2 | h2 <;>
    rw [h1, h2] <;> rw [h1] at hpe <;> rw [h2] at hqe
  · exact absurd (hdisj ▸ Finset.mem_inter.mpr ⟨hpe, hqe⟩) (Finset.notMem_empty e)
  · exact absurd (hdisj ▸ Finset.mem_inter.mpr ⟨hqe, hpe⟩) (Finset.notMem_empty e)

/-- ... and it is **not** a graph with at most one cycle: the two triangles are both cycles. -/
def bowT1 : bow.Walk 0 0 :=
  .cons (show bow.Adj 0 1 by decide) (.cons (show bow.Adj 1 2 by decide)
    (.cons (show bow.Adj 2 0 by decide) .nil))
def bowT2 : bow.Walk 0 0 :=
  .cons (show bow.Adj 0 3 by decide) (.cons (show bow.Adj 3 4 by decide)
    (.cons (show bow.Adj 4 0 by decide) .nil))

theorem bow_not_hasAtMostOneCycle : ¬ HasAtMostOneCycle bow := by
  intro h
  have hc1 : bowT1.IsCycle := by
    rw [Walk.isCycle_def]; exact ⟨⟨by decide⟩, by simp [bowT1], by decide⟩
  have hc2 : bowT2.IsCycle := by
    rw [Walk.isCycle_def]; exact ⟨⟨by decide⟩, by simp [bowT2], by decide⟩
  have := h bowT1 bowT2 hc1 hc2
  have hmem : s(0, 1) ∈ bowT1.edges.toFinset := by decide
  rw [this] at hmem
  revert hmem; decide

/-- **The payoff**: the classification applies to a genuine two-cycle cactus. -/
theorem bow_eccAt_three : bow.ECCAt 3 := isCactus_ecc_of_three_le bow le_rfl bow_isCactus

/-- ... at every list size above two, on the same one line. -/
theorem bow_eccAt_of_three_le {k : ℕ} (hk : 3 ≤ k) : bow.ECCAt k :=
  isCactus_ecc_of_three_le bow hk bow_isCactus

end ListColoring.CactusExamples

#print axioms ListColoring.CactusExamples.not_isCactus_K4
#print axioms ListColoring.CactusExamples.isCactus_C3
#print axioms ListColoring.CactusExamples.bow_isCactus
#print axioms ListColoring.CactusExamples.bow_not_hasAtMostOneCycle
#print axioms ListColoring.CactusExamples.bow_eccAt_of_three_le
