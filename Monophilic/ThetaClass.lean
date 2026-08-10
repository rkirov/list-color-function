/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.RubinHard

/-!
# Scratch
-/

open Finset

namespace Monophilic

open SimpleGraph

section Scratch

/-- Adjacency probe. -/
private def probe (a b c : ℕ) : List (ℕ × ℕ) :=
  ((List.range (a + b + c - 1)).flatMap fun x =>
    (List.range (a + b + c - 1)).map fun y => (x, y)).filter fun p =>
      decide (thetaGenAdjB a b c p.1 p.2 = true)

#eval probe 3 3 3
#eval probe 1 3 3
#eval probe 2 2 4

end Scratch

end Monophilic
