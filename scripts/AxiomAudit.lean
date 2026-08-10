/-
Axiom audit.

Run with `lake env lean scripts/AxiomAudit.lean`. Every result below must depend only on Lean's
three standard axioms — `propext`, `Classical.choice`, `Quot.sound`. In particular `sorryAx`
appearing in the output would mean a proof is incomplete, and `Lean.ofReduceBool` would mean a proof
had been closed by kernel-external evaluation rather than by the kernel.

CI enforces this (see `.github/workflows/ci.yml`); it is not merely informational.

(The companion check in CI greps these files for the corresponding tactic names. That grep is
deliberately crude and cannot distinguish code from prose, so those names are avoided in the text
here — do not reintroduce them.)
-/
import Monophilic

open SimpleGraph Monophilic

/-! ### Core counting API -/
#print axioms SimpleGraph.col_image_of_injOn
#print axioms SimpleGraph.col_const_eq_colConst
#print axioms SimpleGraph.colConst_pos_iff_colorable
#print axioms SimpleGraph.monophilic_of_not_colorable
#print axioms SimpleGraph.not_monophilic_of_colorable_of_not_choosable
#print axioms SimpleGraph.colFix_none_eq_col_delNone
#print axioms SimpleGraph.col_eq_sum_delNone
#print axioms SimpleGraph.col_sum
#print axioms SimpleGraph.monophilic_iso

/-! ### Lemma 1 and Kostochka–Sidorenko -/
#print axioms SimpleGraph.Monophilic.coneOn
#print axioms SimpleGraph.monophilic_top
#print axioms SimpleGraph.monophilic_cliqueTower
#print axioms SimpleGraph.monophilic_cliqueTower_of_isEmpty

/-! ### Lemma 2 and Lemma 4 -/
#print axioms SimpleGraph.col_bridge
#print axioms SimpleGraph.col_swapRight_add
#print axioms SimpleGraph.exists_nested_of_bridge
#print axioms Monophilic.col_lt_col_of_ssubset

/-! ### Lemma 3 -/
#print axioms Monophilic.pathA_sub_pathB
#print axioms Monophilic.pathA_closed_form
#print axioms Monophilic.col_pathAssign
#print axioms Monophilic.pathSplitIso
#print axioms Monophilic.min_pathA_pathB_le_col
#print axioms Monophilic.isPathShape_parity_of_minimizing

/-! ### Theorem 1 -/
#print axioms Monophilic.colConst_closePath
#print axioms Monophilic.monophilic_closePath
#print axioms Monophilic.two_le_col_closePath_of_not_const
#print axioms Monophilic.rotIso
#print axioms Monophilic.monophilic_closePath_two
#print axioms Monophilic.monophilic_closePath_of_two_le

/-! ### Lemma 5, Lemma 6, Theorem 2 -/
#print axioms SimpleGraph.monophilic_addPendant_iff
#print axioms SimpleGraph.monophilic_pendantTower_iff
#print axioms SimpleGraph.monophilic_K23
#print axioms Monophilic.not_monophilic_theta
#print axioms SimpleGraph.monophilic_two_iff_of_rubin

/-! ### Section 5 building block -/
#print axioms SimpleGraph.ERT.col_L₀_eq_zero
#print axioms SimpleGraph.ERT.not_choosable
#print axioms SimpleGraph.ERT.not_monophilic

/-! ### Rubin's theorem: the direction that is proved -/
#print axioms SimpleGraph.Choosable.mono
#print axioms SimpleGraph.Choosable.comap
#print axioms SimpleGraph.choosable_pendantTower_iff
#print axioms Monophilic.choosable_two_closePath_of_odd
#print axioms Monophilic.not_choosable_two_closePath_of_even
#print axioms Monophilic.choosable_theta
#print axioms Monophilic.choosable_two_of_rubinFamily
#print axioms SimpleGraph.monophilic_two_iff_of_rubin_hard

/-! ### The list color function -/
#print axioms SimpleGraph.listColorFunction
#print axioms SimpleGraph.monophilic_iff_listColorFunction_eq
#print axioms Monophilic.monophilic_closePath_all
#print axioms Monophilic.listColorFunction_closePath
#print axioms Monophilic.colConst_closePath_chromatic
#print axioms Monophilic.listColorFunction_closePath_chromatic

/-! ### The chromatic polynomial (Whitney subset expansion) -/
#print axioms SimpleGraph.chromaticPolynomial
#print axioms SimpleGraph.eval_chromaticPolynomial
#print axioms SimpleGraph.chromaticPolynomial_bot
#print axioms SimpleGraph.monophilic_iff_listColorFunction_eq_eval
