# Minimum list-coloring research notes

Current reading order (2026-08-10):

1. [`min_list_coloring_research.md`](min_list_coloring_research.md) gives the general spectrum
   framework, exact disjoint-union and leaf reductions, the complete `2`-choosable classification,
   the deletion-shadow reformulation of monotonicity, and theta/cactus research directions.
2. [`rooted_cycle_product_proof.md`](rooted_cycle_product_proof.md) improves the cactus discussion:
   it proves the rooted-cycle product inequality, completely determines the spectrum for cycle
   bouquets, and proves uniform minimality for cacti with at most one even cycle.
3. [`grid_ladder_three_um.md`](grid_ladder_three_um.md) proves that every ladder \(P_2\square P_n\) is
   3-uniform-minimal (\(P_\ell=P=2\cdot 3^n\)), records the column-transfer lemma used in the proof,
   and explains why the \(K_{2,r}\) large-\(r\) defect does not embed in grids (so the general
   \(m\times n\) grid 3-UM question remains open but is not killed by that counterexample).
   Verification: `grid_ladder_verify.py`.

The short `rooted_cycles_and_cacti.md` file is only the scratch marker made when the second result
was first identified; the complete statement and proof are in `rooted_cycle_product_proof.md`.

