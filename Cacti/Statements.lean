/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.RootedProfile
import Cacti.GMFinal

/-!
# The cactus classification: target statements

## What is claimed

Every statement below is proved outright — CI greps this directory for unproved steps, as it
does `ListColoring/` — and each depends on
exactly `propext`, `Classical.choice` and `Quot.sound` — asserted by `#print axioms` at the foot
of this file. The source of record for the mathematics is
`ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md` (adversarially reviewed in
`ADVERSARIAL_REVIEW_2026-08-15_HANDOFF.md`); the numbered theorems cited are the UM-series in
the research notes.

The routes: `isCactus_ecc_two_iff` through Kirov–Naimi Theorem 2 and Rubin;
`isCactus_ecc_of_four_le` (UM-108) through the pair-bound block induction of
`Cacti/Induction.lean`; `isCactus_ecc_three` (UM-105) through the GM induction
`cactus_gm_bound` of `Cacti/GMFinal.lean`, whose cycle blocks are the balanced core
(`Cacti/BalancedCore.lean`, UM-025) for odd cycles and the tensor capacity
`cycle_gm_bound_even` (UM-104) for even ones.

**Nothing in `ListColoring/` or `Cacti/Defs.lean`–`Cacti/RootedProfile.lean` may depend on this
file.** The proved layers import upward into this file, never the reverse.

## Provenance

These are results of the 2026-08 AI research collaboration on this repository, not of the
Kirov–Naimi paper. The `k = 2` classification (`isCactus_ecc_two_iff`) *does* route through the
formalized Kirov–Naimi Theorem 2 and Rubin's theorem via `ListColoring.ecc_two_iff`.
-/

namespace ListColoring

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Every cactus is `k`-ECC for `k ≥ 4`** (UM-108, handoff §6): the pair-invariant induction
`cactus_pair_bound` run with trivial weights at an arbitrary root, closed by the terminal
AM–GM `PairBound.card_mul_le_sum` — this is (6.16). -/
theorem isCactus_ecc_of_four_le {k : ℕ} (hk : 4 ≤ k) (hG : IsCactus G) : G.ECCAt k := by
  classical
  intro L hL
  obtain ⟨r⟩ := hG.1.nonempty
  -- the induction at `r`, with the weights trivial: a pair bound on the rooted profile
  have hpair : ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
      (rootedCol G (constList V k) r 0) ^ 2 ≤ rootedCol G L r c * rootedCol G L r d := by
    intro c hc d hd hcd
    have h := cactus_pair_bound (Fintype.card V) V G rfl hk hG L hL (fun _ _ => 1) (fun _ => 1)
      (fun v c' _ d' _ _ => by simp) r c hc d hd hcd
    rw [rootedWcol_one, rootedWcol_one] at h
    simpa using h
  -- read the profile off an enumeration of the root's list
  obtain ⟨σ, hσmem, hσinj⟩ := exists_enum (hL r)
  have hx : ∀ i : Fin k, (0 : ℝ) ≤ (rootedCol G L r (σ i) : ℝ) := fun _ => by positivity
  have hpb : PairBound ((rootedCol G (constList V k) r 0 : ℕ) : ℝ)
      (fun i : Fin k => (rootedCol G L r (σ i) : ℝ)) := by
    intro i j hij
    have h := hpair (σ i) (hσmem i) (σ j) (hσmem j) (fun hcon => hij (hσinj hcon))
    show ((rootedCol G (constList V k) r 0 : ℕ) : ℝ) ^ 2 ≤
      ((rootedCol G L r (σ i) : ℕ) : ℝ) * ((rootedCol G L r (σ j) : ℕ) : ℝ)
    exact_mod_cast h
  have hsum := PairBound.card_mul_le_sum (by omega : 2 ≤ k) (by positivity) hx hpb
  -- summing over indices is summing over the root's list
  have hre : ∑ i : Fin k, (rootedCol G L r (σ i) : ℝ)
      = ((∑ c ∈ L r, rootedCol G L r c : ℕ) : ℝ) := by
    rw [Nat.cast_sum, ← enum_image (hL r) hσmem hσinj,
      Finset.sum_image (fun i _ j _ h => hσinj h)]
  rw [hre] at hsum
  have hnat : k * rootedCol G (constList V k) r 0 ≤ ∑ c ∈ L r, rootedCol G L r c := by
    exact_mod_cast hsum
  rw [col_eq_sum_rootedCol G L r,
    ← card_mul_rootedCol_constList G k r (c := 0) (Finset.mem_range.mpr (by omega))]
  exact hnat

/-- **Every cactus is `3`-ECC** (UM-105, handoff §5).

The invariant is GM dominance rather than the pair bound —
at `k = 3` the pair bound is false — so the induction carries
`(A · ∏ᵥ W v)³ ≤ ∏_{c ∈ L r} rootedWcol G L w r c` against weights with
`(W v)³ ≤ ∏_{c ∈ L v} w v c`,
and closes with `card_mul_le_sum_of_pow_le_prod`, which asks only for the product bound. Its case
split is `exists_cut_split_or_cyclic_index_of_three_le`: the one-vertex and single-edge bases (the
latter is `(a+b)(b+c)(c+a) ≥ 8abc`), the cut-vertex step — `rootedWcol_absorb` and two uses of the
induction hypothesis, exactly as `pair_bound_of_cut` does it at `k ≥ 4` — and the cycle blocks.
The cycle blocks are the real work: UM-104, the full tensor capacity of every even cycle
(handoff §5.2–§5.6), and the balanced core UM-025 for the odd ones. -/
theorem isCactus_ecc_three (hG : IsCactus G) : G.ECCAt 3 := by
  classical
  intro L hL
  obtain ⟨r⟩ := hG.1.nonempty
  -- the induction at `r`, with the weights trivial: GM dominance of the rooted profile
  have hgm : (rootedCol G (constList V 3) r 0) ^ 3 ≤ ∏ c ∈ L r, rootedCol G L r c := by
    have h := cactus_gm_bound (Fintype.card V) V G rfl hG L hL (fun _ _ => 1) (fun _ => 1)
      (fun v => by simp) r
    simp only [rootedWcol_one, Finset.prod_const_one, mul_one] at h
    exact h
  -- read the profile off an enumeration of the root's list, and close by AM-GM
  obtain ⟨σ, hσmem, hσinj⟩ := exists_enum (hL r)
  have hx : ∀ i : Fin 3, (0 : ℝ) ≤ (rootedCol G L r (σ i) : ℝ) := fun _ => by positivity
  have hprod : ((rootedCol G (constList V 3) r 0 : ℕ) : ℝ) ^ 3
      ≤ ∏ i : Fin 3, ((rootedCol G L r (σ i) : ℕ) : ℝ) := by
    have hre : ∏ i : Fin 3, ((rootedCol G L r (σ i) : ℕ) : ℝ)
        = ((∏ c ∈ L r, rootedCol G L r c : ℕ) : ℝ) := by
      rw [Nat.cast_prod, ← enum_image (hL r) hσmem hσinj,
        Finset.prod_image (fun i _ j _ h => hσinj h)]
    rw [hre]
    exact_mod_cast hgm
  have hsum := card_mul_le_sum_of_pow_le_prod (by norm_num : 0 < 3) (by positivity) hx hprod
  have hre : ∑ i : Fin 3, ((rootedCol G L r (σ i) : ℕ) : ℝ)
      = ((∑ c ∈ L r, rootedCol G L r c : ℕ) : ℝ) := by
    rw [Nat.cast_sum, ← enum_image (hL r) hσmem hσinj,
      Finset.sum_image (fun i _ j _ h => hσinj h)]
  rw [hre] at hsum
  have hnat : 3 * rootedCol G (constList V 3) r 0 ≤ ∑ c ∈ L r, rootedCol G L r c := by
    exact_mod_cast hsum
  rw [col_eq_sum_rootedCol G L r,
    ← card_mul_rootedCol_constList G 3 r (c := 0) (Finset.mem_range.mpr (by omega))]
  exact hnat

/-- **Every cactus is `k`-ECC for `k ≥ 3`** (UM-105 for `k = 3`, UM-108 for `k ≥ 4`).
Text proof: handoff §5–§6. -/
theorem isCactus_ecc_of_three_le {k : ℕ} (hk : 3 ≤ k) (hG : IsCactus G) : G.ECCAt k := by
  rcases eq_or_lt_of_le hk with rfl | hk'
  · exact isCactus_ecc_three G hG
  · exact isCactus_ecc_of_four_le G (by omega) hG

/-- **The exact `k = 2` cactus classification**: a connected cactus is `2`-ECC iff it has at
most one cycle or contains an odd cycle. Routes through the formalized
`ListColoring.ecc_two_iff` (Kirov–Naimi Theorem 2 + Rubin) and the cactus core analysis
(handoff §3): forward by the four-way core case split (`K₂,₃` impossible in a cactus,
vertex/cycle cores transported by cycle descent), reverse by leaf peeling.

The odd cycle is `SimpleGraph.HasOddCycle`, a subgraph copy of Mathlib's `cycleGraph n` for odd
`n ≥ 3` — the same predicate Kirov–Naimi Theorem 2 is stated with, not the internal
`closePath` encoding the proof runs on. -/
theorem isCactus_ecc_two_iff (hG : IsCactus G) :
    G.ECCAt 2 ↔ HasAtMostOneCycle G ∨ SimpleGraph.HasOddCycle G := by
  rw [SimpleGraph.hasOddCycle_iff]
  constructor
  · exact hasAtMostOneCycle_or_hasOddCycle_of_ecc_two hG
  · rintro (h | h)
    · rcases coreIsVertex_or_coreIsCycle (Fintype.card V) V G rfl hG.1 h with hv | hc
      · exact ecc_of_coreIsVertex hv 2
      · exact ecc_of_coreIsCycle hc 2
    · exact ecc_two_of_hasOddCycle h

/-- **The full cactus spectrum** (handoff Theorem A): a connected cactus is ECC at every size
iff it has at most one cycle or contains an odd cycle. Below `2` the property is vacuous, at `2`
it is the classification, and above it every cactus is ECC. -/
theorem isCactus_ecc_iff (hG : IsCactus G) :
    G.ECC ↔ HasAtMostOneCycle G ∨ SimpleGraph.HasOddCycle G := by
  refine ⟨fun h => (isCactus_ecc_two_iff G hG).mp (h 2), fun h => ecc_of_forall_two_le ?_⟩
  intro n hn
  rcases eq_or_lt_of_le hn with rfl | hn'
  · exact (isCactus_ecc_two_iff G hG).mpr h
  · exact isCactus_ecc_of_three_le G (by omega) hG

end ListColoring

#print axioms ListColoring.isCactus_ecc_of_four_le
#print axioms ListColoring.isCactus_ecc_three
#print axioms ListColoring.isCactus_ecc_of_three_le
#print axioms ListColoring.isCactus_ecc_two_iff
#print axioms ListColoring.isCactus_ecc_iff
