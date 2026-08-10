import Mathlib
/-!
# List coloring and `n`-monophilic graphs — the challenge statements

This file is the *statement surface* of the `graph_coloring` development, a formalization of

> Slobodan Kirov and Ramin Naimi, *List coloring and `n`-monophilic graphs*,
> Ars Combinatoria (arXiv:1004.5183),

together with the chromatic-polynomial / list-color-function reformulation and Donner's theorem.
Every declaration below is stated exactly as in the library and left with a placeholder body, so
that the comparator can check a submission's statements against these.  Compiling this file is
*expected* to report "declaration uses `sorry`" for every declaration in it — that is the point.

`Submission.lean` supplies the real definitions and proofs by importing `Monophilic`.

## What is in here

**Vocabulary (`definition_names` in `config.json`).** Every definition that occurs in one of the
statements below, plus the paper's named constructions:

* counting: `ListAssignment`, `IsNListAssignment`, `constList`, `IsProperColoring`, `colorings`,
  `col`, `colConst`, `colFix`, `colAvoid`, `Monophilic`, `Choosable`, `Minimizing`, `colCounts`,
  `listColorFunction`, `compCount`, `chromaticPolynomial`, `listCount`, `compInter`, `edgeGraph`;
* constructions: `coneOn`, `addPendant`, `addPendantPair`, `delNone`, `inducedList`, `bridge`,
  `swapRight`, `TowerV`, `TowerData`, `pendantTower`, `CliqueTowerData`, `cliqueTower`,
  `CliqueTowerData.IsSimplicial`, `ERT.K`, `ERT.L₀`;
* paths, cycles and thetas: `PathV`, `pathG`, `pathStart`, `pathEnd`, `pathVtx`, `pathA`, `pathB`,
  `pathAssign`, `pathSplitIso`, `IsNNAssign`, `IsPathShape`, `closePath`, `rotIso`, `reach`,
  `ThetaV`, `theta`, `RubinFamily`;
* the `DecidableRel` / `Fintype` / `DecidableEq` instances that the statements above elaborate
  through (`instDecidableRelPathG`, `coneOn.instDecidableRel`, …).  These are part of the
  statements whether or not one likes it: `G.col L` does not typecheck without them.

Three definitions carry their real bodies rather than a placeholder, because other *statements*
need them to reduce: `ListAssignment` (its values are applied as functions), `ThetaV` and `ERT.K`
(their `Fintype` / `DecidableRel` instances are found by unfolding), and `edgeGraph` (likewise).
The comparator never inspects the body of a `definition_names` entry, so this gives nothing away.

The library also contains a substantial number of *internal* helper definitions — `pathSplitIsoAux`,
`coneAdj`, `addPendantAdj`, `addPendantPairAdj`, `pathInterior`, `pathIdx`, `pathVtxEquiv`,
`rotEquiv`, `pathSplitEquiv`, `pathGCongr`, `optionSumEquiv`, `thetaBaseOf`, `thetaOf`, `lvl`,
`levelAssign`, `thetaAssign`, `eraseEnds`, `thetaWitness`, `optAssign`, `endPair`, `testM'`,
`extendList`, `whitneySum`, `ConstOnEdge`, `edgeDef`, `listInter`, `compFinset`, `compEdges`,
`rhsL`, `univTowerData`, `topIsoTopOfEquiv`, `towerVEquivFin`, the `#guard` fixtures `L1`, `L4`,
… — which are **deliberately omitted**: they are implementation details of the proofs, not part of
the mathematical statement of any result.  Of the library's 86 non-private top-level
`def`/`abbrev`/`structure` declarations and 26 `instance`s, this file declares the 69 that the
statements below actually mention or that the paper names: 67 of them are listed in
`definition_names`, and the remaining two are the `structure`s `IsNNAssign` and `IsPathShape`,
which the comparator compares structurally (as inductive types) rather than as definition holes,
and which are therefore reproduced here field for field.

**Results (`theorem_names` in `config.json`, 59 entries).** The 55 results audited by
`scripts/AxiomAudit.lean` — of which 51 are theorems and four (`pathSplitIso`, `rotIso`,
`listColorFunction`, `chromaticPolynomial`) are data and so belong to `definition_names` — together
with the eight theorems of `Monophilic.Threshold` (the explicit threshold and Donner's theorem;
its ninth new declaration, `listCount`, is again data).

## Layout

The sections follow the paper, with dependencies pulled forward where Lean requires it (the path
vocabulary appears with Lemma 4, the tower vocabulary with Kostochka–Sidorenko).
-/

open Finset

/-
`import Mathlib` brings in strictly more `Fintype` instances than `Monophilic`'s own imports do; in
particular `SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat` matches `Fintype (Fin 2)`
via `(SimplexCategory.mk 1).toType`, and being declared later it wins by default. That would make
`monophilic_K23`'s *statement* differ from the library's, which elaborates the same `Fintype (Fin 2)`
to `Fin.fintype 2`. Restoring `Fin.fintype`'s precedence keeps every statement below literally the
one the library proves. (Only numerals are affected: for a variable `n`, `Fintype (Fin n)` cannot
match the `SimplexCategory` instance at all.)
-/
attribute [local instance 2000] Fin.fintype

namespace SimpleGraph

/-! ### The core counting API

Kirov–Naimi §1–2: list assignments, the coloring count `col(G, L)`, its constant-list
specialization `col(G, n)`, and the definitions of `n`-monophilic and `n`-choosable.
-/

section ListAssignmentDefs

universe u_2

/-- A **list assignment** for a graph on `V` gives each vertex a finite set of allowed colors. -/
abbrev ListAssignment (V : Type u_2) : Type u_2 := V → Finset ℕ

/-- The constant list assignment sending every vertex to `{0, 1, …, n-1}`; the paper's `[n]`. -/
def constList (V : Type u_2) (n : ℕ) : ListAssignment V := sorry

end ListAssignmentDefs

/-- An **`n`-list assignment** gives every vertex a list of exactly `n` colors. -/
def IsNListAssignment {V : Type*} (L : ListAssignment V) (n : ℕ) : Prop := sorry

/-- `f` is a proper coloring of `G`: adjacent vertices get distinct colors. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) (f : V → ℕ) : Prop := sorry

/-- The finset of proper colorings of `G` drawn from the lists `L`. -/
def colorings {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : Finset (V → ℕ) := sorry

/-- `col(G, L)`: the number of proper colorings of `G` from the list assignment `L`. -/
def col {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : ℕ := sorry

/-- `col(G, n)`: the number of proper colorings of `G` from the constant list `{0, …, n-1}`. -/
def colConst {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : ℕ := sorry

/-- `col(G, L, v, c)`: the number of colorings of `G` from `L` assigning color `c` to vertex `v`. -/
def colFix {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) (v : V) (c : ℕ) : ℕ := sorry

/-- `G` is **`n`-monophilic** when the number of list colorings is minimized by the constant list
assignment, among all assignments of lists of size `n`. -/
def Monophilic {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop := sorry

/-- `G` is **`n`-choosable** if it admits a coloring from every `n`-list assignment. -/
def Choosable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop := sorry

/-- `L` is **minimizing** for `G` when no list assignment with the same list sizes admits fewer
colorings. -/
def Minimizing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : Prop := sorry

/-- Renaming the colors by a function injective on the colors actually available does not change
the number of list colorings. -/
theorem col_image_of_injOn {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {L : ListAssignment V} {e : ℕ → ℕ}
    (he : Set.InjOn e (⋃ v, (L v : Set ℕ))) :
    G.col (fun v => (L v).image e) = G.col L := sorry

/-- Colorings from a constant list assignment are counted by `col(G, n)`, for any `n`-element set
of colors. -/
theorem col_const_eq_colConst {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset ℕ} {n : ℕ} (hs : s.card = n) :
    G.col (fun _ => s) = G.colConst n := sorry

/-- A graph has a coloring from the constant list `{0, …, n-1}` exactly when it is `n`-colorable. -/
theorem colConst_pos_iff_colorable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : ℕ} : 0 < G.colConst n ↔ G.Colorable n := sorry

/-- If `n < χ(G)` then `G` is `n`-monophilic, vacuously — there are no colorings at all from the
constant list. -/
theorem monophilic_of_not_colorable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : ℕ} (h : ¬ G.Colorable n) : G.Monophilic n := sorry

/-- If `χ(G) ≤ n < χ_ℓ(G)` then `G` is *not* `n`-monophilic. -/
theorem not_monophilic_of_colorable_of_not_choosable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
    (hcol : G.Colorable n) (hch : ¬ G.Choosable n) : ¬ G.Monophilic n := sorry

/-! #### Deleting a vertex -/

/-- The graph obtained from `H` by deleting the vertex `none`. -/
abbrev delNone {V : Type*} (H : SimpleGraph (Option V)) : SimpleGraph V := sorry

instance instDecidableRelAdjDelNone {V : Type*} (H : SimpleGraph (Option V))
    [DecidableRel H.Adj] : DecidableRel H.delNone.Adj := sorry

/-- The list assignment induced on `H − none` by assigning the color `c` to `none`. -/
def inducedList {V : Type*} (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
    (M : ListAssignment (Option V)) (c : ℕ) : ListAssignment V := sorry

/-- **The deletion identity.** Colorings of `H` from `M` that give the color `c` to `none`
correspond exactly to colorings of `H − none` from the induced list assignment. -/
theorem colFix_none_eq_col_delNone {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph (Option V)) [DecidableRel H.Adj] (M : ListAssignment (Option V)) {c : ℕ}
    (hc : c ∈ M none) : H.colFix M none c = (H.delNone).col (H.inducedList M c) := sorry

/-- Splitting the colorings of `H` according to the color assigned to the deleted vertex. This is
the recursion used throughout Kirov–Naimi §3. -/
theorem col_eq_sum_delNone {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph (Option V))
    [DecidableRel H.Adj] (M : ListAssignment (Option V)) :
    H.col M = ∑ c ∈ M none, (H.delNone).col (H.inducedList M c) := sorry

/-! #### Disjoint unions and isomorphisms -/

instance instDecidableRelSumAdjSum_monophilic {V W : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj] :
    DecidableRel (G ⊕g H).Adj := sorry

/-- **Colorings multiply over a disjoint union.** -/
theorem col_sum {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (M : ListAssignment (V ⊕ W)) :
    (G ⊕g H).col M = G.col (M ∘ Sum.inl) * H.col (M ∘ Sum.inr) := sorry

/-- **Monophilicity is an isomorphism invariant.** -/
theorem monophilic_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
    (e : G ≃g G') (n : ℕ) : G.Monophilic n ↔ G'.Monophilic n := sorry

/-! ### Lemma 1 and Kostochka–Sidorenko

Adding a vertex joined to a clique preserves `n`-monophilicity (Lemma 1); iterating gives the
Kostochka–Sidorenko corollary for graphs with a simplicial elimination ordering.
-/

/-- **The cone over `K`.** `coneOn G K` is the graph on `Option V` obtained from `G` by adding one
new vertex `none` joined to precisely the vertices in `K`. -/
def coneOn {V : Type*} (G : SimpleGraph V) (K : Finset V) : SimpleGraph (Option V) := sorry

/-- Adjacency in the cone is decidable. -/
instance coneOn.instDecidableRel {V : Type*} (G : SimpleGraph V) (K : Finset V) [DecidableEq V]
    [DecidableRel G.Adj] : DecidableRel (coneOn G K).Adj := sorry

/-- **Kirov–Naimi, Lemma 1.** If `G` is `n`-monophilic and `K` is a clique of `G`, then the graph
obtained from `G` by adding a new vertex joined to `K` is `n`-monophilic. -/
theorem Monophilic.coneOn {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {K : Finset V} (hK : G.IsClique (K : Set V)) {n : ℕ}
    (hG : G.Monophilic n) : (SimpleGraph.coneOn G K).Monophilic n := sorry

/-- **Complete graphs are `n`-monophilic for every `n`.** -/
theorem monophilic_top (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) :
    (⊤ : SimpleGraph V).Monophilic n := sorry

section Tower

universe u

/-- The vertex type of `G` after `k` successive pendant attachments: `V` with `k` extra points. -/
def TowerV (V : Type u) : ℕ → Type u := sorry

instance instDecidableEqTowerV {V : Type u} [DecidableEq V] : (k : ℕ) → DecidableEq (TowerV V k) :=
  sorry

instance instFintypeTowerV {V : Type u} [Fintype V] : (k : ℕ) → Fintype (TowerV V k) := sorry

/-- The data specifying a tower of `k` cone attachments over `V`: at each stage, the finset of
already-existing vertices that the new vertex is joined to. -/
def CliqueTowerData (V : Type u) : ℕ → Type u := sorry

/-- **A tower of cone attachments.** `cliqueTower G k d` is the graph obtained from `G` by adding
`k` new vertices one after another, the `i`-th of them joined to the set recorded in `d`. -/
def cliqueTower {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → CliqueTowerData V k → SimpleGraph (TowerV V k) := sorry

/-- Adjacency in a clique tower is decidable, by recursion on the height of the tower. -/
instance instDecidableRelCliqueTower {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] :
    (k : ℕ) → (d : CliqueTowerData V k) → DecidableRel (cliqueTower G k d).Adj := sorry

/-- **The simplicial condition.** `d.IsSimplicial` says that at every stage of the tower the set of
old vertices to which the new vertex is attached is a clique *of the graph existing at that
stage*. -/
def CliqueTowerData.IsSimplicial {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → CliqueTowerData V k → Prop := sorry

/-- **Kostochka–Sidorenko, inductive form.** If `G` is `n`-monophilic and `d` is a simplicial tower
of cone attachments over `G`, then `cliqueTower G k d` is `n`-monophilic. -/
theorem monophilic_cliqueTower {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : ℕ} (hG : G.Monophilic n) :
    ∀ (k : ℕ) (d : CliqueTowerData V k), CliqueTowerData.IsSimplicial G k d →
      (cliqueTower G k d).Monophilic n := sorry

/-- **The Kostochka–Sidorenko corollary** (Kirov–Naimi, Corollary to Lemma 1): a graph admitting a
simplicial elimination ordering is `n`-monophilic for every `n`.  The ordering is presented
constructively and backwards, as a tower over an empty graph. -/
theorem monophilic_cliqueTower_of_isEmpty {V : Type u} [Fintype V] [DecidableEq V] [IsEmpty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ) (d : CliqueTowerData V k)
    (hd : CliqueTowerData.IsSimplicial G k d) : (cliqueTower G k d).Monophilic n := sorry

end Tower

/-! ### Lemma 2 and Lemma 4

Lemma 2 is the nesting lemma for a graph cut along a bridge; Lemma 4 says that on a path,
enlarging the lists strictly increases the number of colorings.  The path vocabulary is introduced
here because Lemma 4 is about paths.
-/

/-- The **bridged union** `bridge G H v₀ w₀`: the disjoint union `G ⊕g H` together with one extra
edge joining `Sum.inl v₀` to `Sum.inr w₀`. This is the paper's `G₁ ∪ G₂ + v₁v₂`. -/
def bridge {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (v₀ : V) (w₀ : W) :
    SimpleGraph (V ⊕ W) := sorry

/-- Adjacency in a bridged union is decidable. -/
instance instDecidableRelSumAdjBridge {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (v₀ : V) (w₀ : W) : DecidableRel (bridge G H v₀ w₀).Adj := sorry

/-- `colAvoid G L v c`: the number of colorings of `G` from `L` that do **not** give the color `c`
to the vertex `v`. -/
def colAvoid {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) (v : V) (c : ℕ) : ℕ := sorry

/-- `swapRight M c₁ c₂` agrees with `M` on the left-hand side and applies the transposition
`Equiv.swap c₁ c₂` to every list on the right-hand side. -/
def swapRight {V W : Type*} (M : ListAssignment (V ⊕ W)) (c₁ c₂ : ℕ) : ListAssignment (V ⊕ W) :=
  sorry

/-- **The bridged count.** -/
theorem col_bridge {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    {v₀ : V} {w₀ : W} (M : ListAssignment (V ⊕ W)) :
    (bridge G H v₀ w₀).col M
      = ∑ c ∈ M (.inl v₀), G.colFix (M ∘ Sum.inl) v₀ c * H.colAvoid (M ∘ Sum.inr) w₀ c := sorry

/-- **Part (b) of the swap step: the paper's equation (1)**, in subtraction-free form. -/
theorem col_swapRight_add {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    {v₀ : V} {w₀ : W} (M : ListAssignment (V ⊕ W)) {c₁ c₂ : ℕ}
    (h₁ : c₁ ∈ M (.inl v₀)) (h₁' : c₁ ∉ M (.inr w₀)) (h₂' : c₂ ∉ M (.inl v₀)) :
    (bridge G H v₀ w₀).col (swapRight M c₁ c₂)
        + G.colFix (M ∘ Sum.inl) v₀ c₁ * H.colFix (M ∘ Sum.inr) w₀ c₂
      = (bridge G H v₀ w₀).col M := sorry

/-- **Lemma 2 of Kirov–Naimi.** For any list assignment `M` of the bridged union
`bridge G H v₀ w₀` there is an `M'` with the same list sizes, whose lists at the two endpoints of
the bridge are nested, and with `col(bridge, M') ≤ col(bridge, M)`. -/
theorem exists_nested_of_bridge {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    [DecidableRel H.Adj] {v₀ : V} {w₀ : W} (M : ListAssignment (V ⊕ W)) :
    ∃ M' : ListAssignment (V ⊕ W), (∀ x, (M' x).card = (M x).card) ∧
      (M' (.inl v₀) ⊆ M' (.inr w₀) ∨ M' (.inr w₀) ⊆ M' (.inl v₀)) ∧
      (bridge G H v₀ w₀).col M' ≤ (bridge G H v₀ w₀).col M := sorry

/-- `G` with one new pendant vertex `none`, attached to `v`. -/
def addPendant {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) := sorry

instance instDecidableRelOptionAdjAddPendant {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : DecidableRel (G.addPendant v).Adj := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- The vertex type of a path of length `k` (so `k + 1` vertices). -/
def PathV : ℕ → Type := sorry

instance instDecidableEqPathV : (k : ℕ) → DecidableEq (PathV k) := sorry

instance instFintypePathV : (k : ℕ) → Fintype (PathV k) := sorry

/-- The terminal vertex of `pathG k` that was attached last. -/
def pathEnd : (k : ℕ) → PathV k := sorry

/-- The other terminal vertex of `pathG k`. -/
def pathStart : (k : ℕ) → PathV k := sorry

/-- The path of length `k`: `k + 1` vertices in a row. -/
def pathG : (k : ℕ) → SimpleGraph (PathV k) := sorry

instance instDecidableRelPathG : (k : ℕ) → DecidableRel (pathG k).Adj := sorry

/-- **Lemma 4 of Kirov–Naimi.** For a path, enlarging the lists *strictly* increases the number of
colorings, provided the larger assignment gives at least two colors to every vertex. -/
theorem col_lt_col_of_ssubset (k : ℕ) {L L' : ListAssignment (PathV k)}
    (hsub : ∀ v, L v ⊆ L' v) (hne : L ≠ L') (hcard : ∀ v, 2 ≤ (L' v).card) :
    (pathG k).col L < (pathG k).col L' := sorry

/-! ### Lemma 3

The counts `A_k` and `B_k` for the two shapes of `(n, n-1)`-list assignment on a path, the
closed form for `A_k`, and the three parts of Lemma 3.
-/

/-- Paper's `A_k` for `n = m + 2`: the number of colorings of a path of length `k` coming from a
type A list assignment.  `A_0 = m + 1` and `A_{k+1} = (m + 1) * B_k`. -/
def pathA (m : ℕ) : ℕ → ℕ := sorry

/-- Paper's `B_k` for `n = m + 2`: the number of colorings of a path of length `k` coming from a
type B list assignment.  `B_0 = m` and `B_{k+1} = A_k + m * B_k`. -/
def pathB (m : ℕ) : ℕ → ℕ := sorry

/-- Equation (5) of the paper: `A_k - B_k = (-1) ^ k`, as an identity in `ℤ`. -/
theorem pathA_sub_pathB (m k : ℕ) : ((pathA m k : ℤ) - (pathB m k : ℤ)) = (-1) ^ k := sorry

/-- Closed form for `A_k`, cleared of the division:
`(m + 2) * A_k = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k)`. -/
theorem pathA_closed_form (m k : ℕ) :
    ((m + 2) * pathA m k : ℤ) = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k) := sorry

/-- The `(n, n-1)`-list assignment on the path of length `k` missing color `x` at `pathEnd` and
color `y` at `pathStart`; type A when `x = y`, type B otherwise. -/
def pathAssign : (k : ℕ) → (n x y : ℕ) → ListAssignment (PathV k) := sorry

/-- **Lemma 3(a), graph side.** The number of colorings of a path of length `k` from an
`(n, n-1)`-list assignment is `A_k` if the assignment is type A and `B_k` if it is type B. -/
theorem col_pathAssign (m : ℕ) :
    ∀ (k x y : ℕ), x < m + 2 → y < m + 2 →
      (pathG k).col (pathAssign k (m + 2) x y) = if x = y then pathA m k else pathB m k := sorry

/-- **Cutting a path at an edge.** Deleting the edge between the vertices numbered `a` and `a + 1`
of the path of length `a + b + 1` exhibits it as
`bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)`. -/
def pathSplitIso (a b : ℕ) :
    pathG (a + b + 1) ≃g bridge (pathG a) (pathG b) (pathStart a) (pathEnd b) := sorry

/-- The vertex numbered `i` of the path of length `k`, counting from `pathEnd k` (number `0`)
towards `pathStart k` (number `k`). -/
def pathVtx : (k : ℕ) → ℕ → PathV k := sorry

/-- An **`(n, n-1)`-list assignment** for the path of length `k`, with `n = m + 2`: the two
terminal vertices get `m + 1` colors and every interior vertex gets `m + 2`. -/
structure IsNNAssign (k m : ℕ) (L : ListAssignment (PathV k)) : Prop where
  card_pathEnd : (L (pathEnd k)).card = m + 1
  card_pathStart : (L (pathStart k)).card = m + 1
  card_interior : ∀ v, v ≠ pathEnd k → v ≠ pathStart k → (L v).card = m + 2

/-- The shape of the `(n, n-1)`-list assignments of Lemma 3, with `n = m + 2`: interior lists all
equal to a common palette `S`, the list at `pathEnd k` equal to `S \ {x}` and the list at
`pathStart k` equal to `S \ {y}`.  **Type A** when `x = y`, **type B** when `x ≠ y`. -/
structure IsPathShape (k m : ℕ) (L : ListAssignment (PathV k)) (S : Finset ℕ) (x y : ℕ) :
    Prop where
  card_palette : S.card = m + 2
  mem_left : x ∈ S
  mem_right : y ∈ S
  apply_pathEnd : L (pathEnd k) = S.erase x
  apply_pathStart : L (pathStart k) = S.erase y
  apply_interior : ∀ i, 0 < i → i < k → L (pathVtx k i) = S

/-- **Lemma 3(b) of Kirov–Naimi.** Every `(n, n-1)`-list assignment on the path of length `k`
admits at least `min (A_k, B_k)` colorings. -/
theorem min_pathA_pathB_le_col {k m : ℕ} {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L) :
    min (pathA m k) (pathB m k) ≤ (pathG k).col L := sorry

/-- **Lemma 3(c) of Kirov–Naimi.** For `n ≥ 3` and a path with at least one edge, a minimizing
`(n, n-1)`-list assignment is type A when `k` is odd and type B when `k` is even. -/
theorem isPathShape_parity_of_minimizing {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L) (hmin : (pathG k).Minimizing L) :
    ∃ S x y, IsPathShape k m L S x y ∧ ((Odd k ∧ x = y) ∨ (Even k ∧ x ≠ y)) := sorry

end Monophilic

/-! ### Theorem 1: every cycle is `n`-monophilic

`closePath k` is the path of length `k` with its two ends joined, i.e. the cycle on `k + 1`
vertices once `2 ≤ k`.
-/

namespace SimpleGraph

/-- `G` with one new vertex `none`, joined to both `u` and `v`. -/
def addPendantPair {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) := sorry

instance instDecidableRelAddPendantPair {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (u v : V) : DecidableRel (G.addPendantPair u v).Adj := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- The path of length `k` closed up: `pathG k` together with one extra edge joining its two
terminal vertices.  For `k ≥ 2` this is the cycle on `k + 1` vertices. -/
def closePath : (k : ℕ) → SimpleGraph (PathV k) := sorry

instance instDecidableRelClosePath : (k : ℕ) → DecidableRel (closePath k).Adj := sorry

/-- **Kirov–Naimi's `col(C, n) = n · A_{k-2}`** for a cycle `C` on `k` vertices; here `closePath k`
has `k + 1` vertices, so the index is `k - 1`. -/
theorem colConst_closePath (m k : ℕ) (hk : 1 ≤ k) :
    (closePath k).colConst (m + 2) = (m + 2) * pathA m (k - 1) := sorry

/-- **Theorem 1 of Kirov–Naimi, for `n ≥ 3`.** -/
theorem monophilic_closePath {m k : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    (closePath k).Monophilic (m + 2) := sorry

/-- The colors available at `pathStart k` to a coloring of `pathG k` from `L` that gives the color
`c` to `pathEnd k`. -/
def reach (k : ℕ) (L : ListAssignment (PathV k)) (c : ℕ) : Finset ℕ := sorry

/-- **The rotation is an automorphism of the cycle.** -/
def rotIso {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1)) : closePath k ≃g closePath k := sorry

/-- **`2 ≤ col(C, L)` for every non-constant `2`-list assignment on a cycle.** -/
theorem two_le_col_closePath_of_not_const {k : ℕ} (hk : 1 ≤ k) {L : ListAssignment (PathV k)}
    (hcard : ∀ v, (L v).card = 2) (hnc : ∃ v, L v ≠ L (pathEnd k)) :
    2 ≤ (closePath k).col L := sorry

/-- **The case `n = 2` of Theorem 1.** A cycle on an even number of vertices is `2`-monophilic;
`closePath k` has `k + 1` vertices, so `Odd k` says that number is even. -/
theorem monophilic_closePath_two {k : ℕ} (hk : Odd k) : (closePath k).Monophilic 2 := sorry

/-- **Theorem 1 of Kirov–Naimi in full: every cycle is `n`-monophilic, for every `n ≥ 2`.** -/
theorem monophilic_closePath_of_two_le {k m : ℕ} (hk : 2 ≤ k) :
    (closePath k).Monophilic (m + 2) := sorry

end Monophilic

/-! ### Lemma 5, Lemma 6 and Theorem 2

Lemma 5 is the core reduction (pendant attachments do not change monophilicity), Lemma 6 is
`K₂,₃`, and Theorem 2 is the characterization of the `2`-monophilic graphs, relative to Rubin's
theorem.
-/

namespace SimpleGraph

section PendantTower

universe u

/-- The data specifying a tower of `k` pendant attachments: for each step, the already-existing
vertex at which the new pendant vertex is attached. -/
def TowerData (V : Type u) : ℕ → Type u := sorry

end PendantTower

/-- **A tower of pendant attachments.** `pendantTower G k d` is the graph obtained from `G` by
attaching `k` pendant vertices one after another. -/
def pendantTower {V : Type*} (G : SimpleGraph V) :
    (k : ℕ) → TowerData V k → SimpleGraph (TowerV V k) := sorry

section PendantTowerInst

universe u

instance instDecidableRelPendantTower {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] :
    (k : ℕ) → (d : TowerData V k) → DecidableRel (pendantTower G k d).Adj := sorry

end PendantTowerInst

/-- The pendant step for `SimpleGraph.addPendant`. -/
theorem monophilic_addPendant_iff {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (v : V) (n : ℕ) :
    (G.addPendant v).Monophilic n ↔ G.Monophilic n := sorry

/-- **Kirov–Naimi, Lemma 5.** A graph built from `G` by any finite sequence of pendant attachments
is `n`-monophilic if and only if `G` is; equivalently, a graph is `n`-monophilic iff its core is. -/
theorem monophilic_pendantTower_iff {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (n : ℕ) :
    ∀ (k : ℕ) (d : TowerData V k), (pendantTower G k d).Monophilic n ↔ G.Monophilic n := sorry

/-- Adjacency in a complete bipartite graph is decidable. -/
instance instDecidableRelCompleteBipartiteGraphAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj := sorry

/-- **Lemma 6 of Kirov–Naimi.** `K₂,₃` is `2`-monophilic. -/
theorem monophilic_K23 : (completeBipartiteGraph (Fin 2) (Fin 3)).Monophilic 2 := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- The vertex type of `θ_{2,2,2m}`. -/
abbrev ThetaV (m : ℕ) : Type := Option (Option (PathV (2 * m)))

/-- The theta graph `θ_{2,2,2m}`. -/
def theta (m : ℕ) : SimpleGraph (ThetaV m) := sorry

instance instDecidableRelTheta (m : ℕ) : DecidableRel (theta m).Adj := sorry

/-- **`θ_{2,2,2m}` is not `2`-monophilic for `m ≥ 2`.** -/
theorem not_monophilic_theta (m : ℕ) (hm : 2 ≤ m) : ¬ (theta m).Monophilic 2 := sorry

end Monophilic

namespace SimpleGraph

/-- **Kirov–Naimi, Theorem 2, relative to Rubin's theorem.**

Rubin's characterization of the `2`-choosable graphs (Erdős–Rubin–Taylor 1980) is borrowed as the
explicit hypothesis `rubin`, with the three alternatives kept abstract so that the loan is visible
in the signature and nothing about cores is smuggled in. -/
theorem monophilic_two_iff_of_rubin {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 ↔
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.Monophilic 2)
    (hcycle : CoreIsEvenCycle → G.Monophilic 2)
    (hK23 : CoreIsTheta 1 → G.Monophilic 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.Monophilic 2) :
    G.Monophilic 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 := sorry

/-! ### Section 5: the Erdős–Rubin–Taylor graph

`K_{n,nⁿ}` is `n`-colorable but not `n`-choosable, hence not `n`-monophilic: the middle regime
`χ(G) ≤ n < χ_ℓ(G)` of Kirov–Naimi p. 2 is nonempty for every `n ≥ 2`.
-/

namespace ERT

/-- Adjacency in a complete bipartite graph is decidable. -/
instance instDecidableRelCompleteBipartiteAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj := sorry

/-- `K_{n,nⁿ}`, the complete bipartite graph whose right side is indexed by the functions
`Fin n → Fin n`. -/
abbrev K (n : ℕ) : SimpleGraph (Fin n ⊕ (Fin n → Fin n)) :=
  completeBipartiteGraph (Fin n) (Fin n → Fin n)

/-- The Erdős–Rubin–Taylor list assignment on `K_{n,nⁿ}`, called `L₀` in Kirov–Naimi §5. -/
def L₀ (n : ℕ) : ListAssignment (Fin n ⊕ (Fin n → Fin n)) := sorry

/-- **The key computation**: `col(K_{n,nⁿ}, L₀) = 0`, i.e. `L₀` admits no proper coloring at all. -/
theorem col_L₀_eq_zero (n : ℕ) : (K n).col (L₀ n) = 0 := sorry

/-- `K_{n,nⁿ}` is **not** `n`-choosable, witnessed by `L₀`. -/
theorem not_choosable (n : ℕ) : ¬ (K n).Choosable n := sorry

/-- Since `K_{n,nⁿ}` is `n`-colorable but not `n`-choosable, it is not `n`-monophilic. -/
theorem not_monophilic (n : ℕ) (hn : 2 ≤ n) : ¬ (K n).Monophilic n := sorry

end ERT

/-! ### Rubin's theorem: the direction that is proved

The `⟸` direction of Rubin's characterization — every graph on Rubin's list is `2`-choosable — is
proved here, which reduces the borrowed hypothesis of Theorem 2 to a one-way implication.
-/

/-- **Choosability passes to subgraphs on the same vertex type.** -/
theorem Choosable.mono {V : Type*} [Fintype V] [DecidableEq V] {G G' : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] {n : ℕ}
    (hG' : G'.Choosable n) (h : G ≤ G') : G.Choosable n := sorry

/-- **Choosability passes to subgraphs on a smaller vertex type.** -/
theorem Choosable.comap {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {W : Type*} [Fintype W] [DecidableEq W] {G' : SimpleGraph W}
    [DecidableRel G'.Adj] {n : ℕ} (hG' : G'.Choosable n) {f : V → W}
    (hf : Function.Injective f) (hadj : ∀ a b, G.Adj a b → G'.Adj (f a) (f b)) :
    G.Choosable n := sorry

/-- **The core reduction for choosability.** For `2 ≤ n`, pendant attachments do not change
`n`-choosability.  This mirrors `SimpleGraph.monophilic_pendantTower_iff`. -/
theorem choosable_pendantTower_iff {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : ℕ} (hn : 2 ≤ n) :
    ∀ (k : ℕ) (d : TowerData V k), (pendantTower G k d).Choosable n ↔ G.Choosable n := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- **An even cycle is `2`-choosable**, as a corollary of Theorem 1. -/
theorem choosable_two_closePath_of_odd {k : ℕ} (hk : Odd k) (hk2 : 2 ≤ k) :
    (closePath k).Choosable 2 := sorry

/-- **An odd cycle is not `2`-choosable.** -/
theorem not_choosable_two_closePath_of_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    ¬ (closePath k).Choosable 2 := sorry

/-- **`θ_{2,2,2m}` is `2`-choosable, for every `m ≥ 1`.** -/
theorem choosable_theta (m : ℕ) (hm : 1 ≤ m) : (theta m).Choosable 2 := sorry

/-- A graph is on **Rubin's list** when it is a single vertex, an even cycle, or `θ_{2,2,2m}`,
stated up to isomorphism. -/
def RubinFamily {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := sorry

/-- **Rubin's theorem, ⟸ direction: every graph on Rubin's list is `2`-choosable.** -/
theorem choosable_two_of_rubinFamily {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : RubinFamily G) : G.Choosable 2 := sorry

end Monophilic

namespace SimpleGraph

/-- **Theorem 2 of Kirov–Naimi, borrowing only the hard direction of Rubin's theorem.** -/
theorem monophilic_two_iff_of_rubin_hard {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 →
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.Monophilic 2)
    (hcycle : CoreIsEvenCycle → G.Monophilic 2)
    (hK23 : CoreIsTheta 1 → G.Monophilic 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.Monophilic 2) :
    G.Monophilic 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 := sorry

/-! ### The chromatic polynomial and the list color function

`P(G, n) = col(G, n)` is built by the Whitney subset expansion, `P_ℓ(G, n)` is the least number of
colorings over all `n`-list assignments, and `n`-monophilicity is exactly `P_ℓ(G, n) = P(G, n)`.
-/

/-- Adjacency in `fromEdgeSet S` is decidable when `S` comes from a `Finset` of edges. -/
instance decidableRelFromEdgeSetCoe {V : Type*} [DecidableEq V] (S : Finset (Sym2 V)) :
    DecidableRel (fromEdgeSet (S : Set (Sym2 V))).Adj := sorry

/-- `c(S)`: the number of connected components of the spanning subgraph of `V` whose edges are
exactly the non-loop elements of `S`. -/
def compCount {V : Type*} [Fintype V] [DecidableEq V] (S : Finset (Sym2 V)) : ℕ := sorry

/-- The **chromatic polynomial** of `G`, defined by the Whitney subset expansion
`∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`. -/
noncomputable def chromaticPolynomial {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Polynomial ℤ := sorry

/-- **Evaluation of the chromatic polynomial counts colorings.** -/
theorem eval_chromaticPolynomial {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    (G.chromaticPolynomial).eval (n : ℤ) = (G.colConst n : ℤ) := sorry

/-- The chromatic polynomial of the edgeless graph is `X ^ |V|`. -/
theorem chromaticPolynomial_bot {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableRel (⊥ : SimpleGraph V).Adj] :
    chromaticPolynomial (⊥ : SimpleGraph V) = Polynomial.X ^ Fintype.card V := sorry

/-- The set of coloring counts achievable by `n`-list assignments. -/
def colCounts {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Set ℕ := sorry

/-- **The list color function** `P_ℓ(G, n)`: the least number of colorings achievable by any
`n`-list assignment. -/
noncomputable def listColorFunction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) : ℕ := sorry

/-- **`n`-monophilicity is exactly `P_ℓ(G, n) = P(G, n)`.** -/
theorem monophilic_iff_listColorFunction_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.Monophilic n ↔ G.listColorFunction n = G.colConst n := sorry

/-- **`P_ℓ(G, n) = P(G, n)` with a genuine polynomial on the right.** -/
theorem monophilic_iff_listColorFunction_eq_eval {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.Monophilic n ↔ (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- **Every cycle is `n`-monophilic, for every `n`** — no hypothesis on `n` at all. -/
theorem monophilic_closePath_all (k n : ℕ) (hk : 2 ≤ k) : (closePath k).Monophilic n := sorry

/-- **`P_ℓ(C, n) = P(C, n)` for every cycle and every `n`** — Theorem 1 in the notation the
literature uses. -/
theorem listColorFunction_closePath (k n : ℕ) (hk : 2 ≤ k) :
    (closePath k).listColorFunction n = (closePath k).colConst n := sorry

/-- **The chromatic polynomial of a cycle, as a closed form**: for the cycle on `v = k + 2`
vertices and `n = m + 2` colors, `col(C, n) = (n-1)^v + (-1)^v (n-1)`. -/
theorem colConst_closePath_chromatic (m k : ℕ) :
    (((closePath (k + 1)).colConst (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) := sorry

/-- The two together: for a cycle on `v = k + 2` vertices and `n = m + 2` colors, the list color
function is exactly `(n-1)^v + (-1)^v (n-1)`. -/
theorem listColorFunction_closePath_chromatic (m k : ℕ) (hk : 1 ≤ k) :
    (((closePath (k + 1)).listColorFunction (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) := sorry

end Monophilic

namespace SimpleGraph

/-! ### An explicit threshold, and Donner's theorem

The Whitney expansion of `col(G, L)` for an *arbitrary* list assignment `L`, an explicit
monophilicity threshold obtained from it, and Donner's theorem (1992): every graph is
`n`-monophilic for all sufficiently large `n`.
-/

/-- The spanning subgraph of `V` with edge set `S` (loops in `S` are discarded). -/
abbrev edgeGraph {V : Type*} (S : Finset (Sym2 V)) : SimpleGraph V :=
  fromEdgeSet (S : Set (Sym2 V))

/-- `⋂_{v ∈ C} L v` for a connected component `C` of `edgeGraph S`. -/
def compInter {V : Type*} [Fintype V] [DecidableEq V] (L : ListAssignment V)
    (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) : Finset ℕ := sorry

/-- The number of colorings of `V` from the lists `L` that are constant on every edge of `S`. -/
def listCount {V : Type*} [Fintype V] [DecidableEq V] (L : ListAssignment V)
    (S : Finset (Sym2 V)) : ℕ := sorry

/-- **The key counting lemma, for arbitrary lists.** A coloring from `L` constant on every edge of
`S` is exactly a choice, for each connected component `C` of `(V, S)`, of a color lying in *all*
the lists of `C`. -/
theorem listCount_eq_prod {V : Type*} [Fintype V] [DecidableEq V] (L : ListAssignment V)
    (S : Finset (Sym2 V)) :
    listCount L S = ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L S C) := sorry

/-- **The Whitney expansion of the list coloring count.** Inclusion–exclusion over the edge set
turns `col(G, L)` into an alternating sum of the counts `listCount L S`. -/
theorem col_eq_sum_powerset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (L : ListAssignment V) :
    (G.col L : ℤ) = ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * (listCount L S : ℤ) := sorry

/-- For the constant list assignment the count is `k ^ c(S)`, recovering the chromatic
polynomial. -/
theorem listCount_constList {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (S : Finset (Sym2 V)) : listCount (constList V k) S = k ^ compCount S := sorry

/-- **An explicit monophilicity threshold.** If the number of colors exceeds `2 ^ m`, where `m` is
the number of edges, then `G` is `k`-monophilic. -/
theorem monophilic_of_two_pow_lt {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (hk : 2 ^ #G.edgeFinset < k) : G.Monophilic k := sorry

/-- **Donner's theorem (1992).** Every graph is `k`-monophilic for all sufficiently large `k`. -/
theorem exists_monophilic_forall_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∃ N, ∀ k, N ≤ k → G.Monophilic k := sorry

/-- The threshold theorem stated as `P_ℓ(G, k) = P(G, k)`. -/
theorem listColorFunction_eq_of_two_pow_lt {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 2 ^ #G.edgeFinset < k) :
    G.listColorFunction k = G.colConst k := sorry

/-- The same, against the genuine chromatic polynomial: for `k > 2 ^ m` the list color function of
*any* graph is the evaluation of its chromatic polynomial. -/
theorem listColorFunction_eq_eval_of_two_pow_lt {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : 2 ^ #G.edgeFinset < k) :
    (G.listColorFunction k : ℤ) = (G.chromaticPolynomial).eval (k : ℤ) := sorry

/-- Donner's theorem for the list color function. -/
theorem exists_listColorFunction_eq_forall_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.listColorFunction k = G.colConst k := sorry

end SimpleGraph
