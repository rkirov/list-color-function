/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The chromatic polynomial, via the Whitney subset expansion
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

instance decidableRelFromEdgeSetCoe (S : Finset (Sym2 V)) :
    DecidableRel (fromEdgeSet (S : Set (Sym2 V))).Adj :=
  fun _ _ => decidable_of_iff' _ fromEdgeSet_adj

/-- Number of connected components of the spanning subgraph with edge set `S`. -/
def compCount (S : Finset (Sym2 V)) : ℕ :=
  Fintype.card (fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Whitney sum evaluated at an integer. -/
def whitneySum (x : ℤ) : ℤ :=
  ∑ S ∈ G.edgeFinset.powerset, (-1) ^ S.card * x ^ compCount S

noncomputable def chromaticPolynomial : Polynomial ℤ :=
  ∑ S ∈ G.edgeFinset.powerset, (-1) ^ S.card * Polynomial.X ^ compCount S

end SimpleGraph

section Check

#guard (⊤ : SimpleGraph (Fin 3)).colConst 3 = 6
#guard (⊤ : SimpleGraph (Fin 3)).whitneySum 3 = 6
#guard (⊤ : SimpleGraph (Fin 3)).whitneySum 4 = 24

end Check
