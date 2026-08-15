/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.RootedProfile
import Cacti.LeafPeeling

/-!
# The cactus classification: target statements

## Read the `sorry`s correctly

Unlike `OpenProblems.lean`, a `sorry` here means **proved on paper, not yet in Lean**. Each
statement below has a complete text proof with exact finite certificates in
`ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md` (adversarially reviewed in
`ADVERSARIAL_REVIEW_2026-08-15_HANDOFF.md`); the numbered theorems cited are the UM-series in
the research notes. The formalization proceeds bottom-up per handoff §11, and each `sorry` below
is expected to be discharged as its layer lands.

**Nothing in `ListColoring/` or `Cacti/Defs.lean`–`Cacti/RootedProfile.lean` may depend on this
file.** The proved layers import upward into this file, never the reverse, so no proved theorem
can silently depend on an unproved statement.

## Provenance

These are results of the 2026-08 AI research collaboration on this repository, not of the
Kirov–Naimi paper. The `k = 2` classification (`isCactus_ecc_two_iff`) *does* route through the
formalized Kirov–Naimi Theorem 2 and Rubin's theorem via `ListColoring.ecc_two_iff`.
-/

namespace ListColoring

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Every cactus is `k`-ECC for `k ≥ 3`** (UM-105 for `k = 3`, UM-108 for `k ≥ 4`).
Text proof: handoff §5–§6. -/
theorem isCactus_ecc_of_three_le {k : ℕ} (hk : 3 ≤ k) (hG : IsCactus G) : G.ECCAt k := by
  sorry

/-- **The exact `k = 2` cactus classification**: a connected cactus is `2`-ECC iff it has at
most one cycle or contains an odd cycle. Routes through the formalized
`ListColoring.ecc_two_iff` (Kirov–Naimi Theorem 2 + Rubin) and the cactus core analysis
(handoff §3): forward by the four-way core case split (`K₂,₃` impossible in a cactus,
vertex/cycle cores transported by cycle descent), reverse by leaf peeling. -/
theorem isCactus_ecc_two_iff (hG : IsCactus G) :
    G.ECCAt 2 ↔ HasAtMostOneCycle G ∨ HasOddCycle G := by
  constructor
  · exact hasAtMostOneCycle_or_hasOddCycle_of_ecc_two hG
  · rintro (h | h)
    · rcases coreIsVertex_or_coreIsCycle (Fintype.card V) V G rfl hG.1 h with hv | hc
      · exact ecc_of_coreIsVertex hv 2
      · exact ecc_of_coreIsCycle hc 2
    · exact ecc_two_of_hasOddCycle h

/-- **The full cactus spectrum** (handoff Theorem A): a connected cactus is ECC at every size
iff it has at most one cycle or contains an odd cycle. -/
theorem isCactus_ecc_iff (hG : IsCactus G) :
    G.ECC ↔ HasAtMostOneCycle G ∨ HasOddCycle G := by
  sorry

end ListColoring
