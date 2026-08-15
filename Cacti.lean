/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Defs
import Cacti.Structure
import Cacti.LeafPeeling
import Cacti.Rooted
import Cacti.Weighted
import Cacti.Rooted
import Cacti.WeightedProfile
import Cacti.Statements

/-!
# Cacti

The cactus ECC classification: every cactus is `k`-ECC for `k ≥ 3`, and a connected cactus is
`2`-ECC iff it has at most one cycle or an odd cycle. Separate from the Kirov–Naimi
formalization in `ListColoring/` (which this library imports, never the reverse). Source of
record: `ai_research_notes/FINAL_CACTI_ECC_HANDOFF.md`.
-/
