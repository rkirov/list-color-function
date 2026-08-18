/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Defs
import Cacti.Structure
import Cacti.LeafPeeling
import Cacti.CutVertex
import Cacti.Rooted
import Cacti.Weighted
import Cacti.Absorb
import Cacti.Uniform
import Cacti.Bridge
import Cacti.Induction
import Cacti.Peel
import Cacti.TransferMatrix
import Cacti.CycleCases
import Cacti.Relabel
import Cacti.BalancedCore
import Cacti.CyclePair
import Cacti.RootedProfile
import Cacti.Three
import Cacti.Tensor
import Cacti.EvenTensor
import Cacti.RefTensor
import Cacti.PathCone
import Cacti.EvenBridge
import Cacti.EvenBase
import Cacti.EvenSplit
import Cacti.C6Branch
import Cacti.LargeBranch
import Cacti.GMFinal
import Cacti.Statements

/-!
# Cacti

The cactus ECC classification: every cactus is `k`-ECC for `k ≥ 3`, and a connected cactus is
`2`-ECC iff it has at most one cycle or an odd cycle. Separate from the Kirov–Naimi
formalization in `ListColoring/` (which this library imports, never the reverse). Source of
record: `ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md`.

The classification is complete: every step is proved, nothing is assumed. Three cases:

* `k = 2` — `isCactus_ecc_two_iff`, through the formalized Kirov–Naimi Theorem 2 and Rubin's
  theorem in `ListColoring/`, plus the cactus core analysis (handoff §3).
* `k ≥ 4` — `isCactus_ecc_of_four_le` (UM-106 through UM-108): the transfer-matrix cycle bound,
  weighted peeling, and the block induction over the cut-vertex decomposition. The invariant is
  the pair bound `A² ≤ x_c · x_d`, and the slack `k - 3 ≥ 1` is what pays for the peeling.
* `k = 3` — `isCactus_ecc_three` (UM-105). The pair bound is false here, so the induction carries
  GM dominance instead (`cactus_gm_bound`, `Cacti/GMFinal.lean`). Its cycle blocks are the whole
  difficulty: odd cycles by the balanced core (UM-025, `Cacti/BalancedCore.lean`), even cycles by
  the tensor capacity `cycle_gm_bound_even` (UM-104), which splits into `C₄`
  (`Cacti/EvenBase.lean`), `C₆` (`Cacti/C6Branch.lean`, UM-096) and `m ≥ 7`
  (`Cacti/LargeBranch.lean`, handoff §5.3–§5.6).
-/
