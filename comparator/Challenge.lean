import Mathlib
/-!
# List coloring and `n`-monophilic graphs — the challenge statements

This file is the *statement surface* of the `graph_coloring` development, a formalization of

> Radoslav Kirov and Ramin Naimi, *List coloring and `n`-monophilic graphs*,
> Ars Combinatoria (arXiv:1004.5183),

together with the chromatic-polynomial / list-color-function reformulation and Donner's theorem.
Every declaration below is stated exactly as in the library and left with a placeholder body, so
that the comparator can check a submission's statements against these.  Compiling this file is
*expected* to report "declaration uses `sorry`" for every declaration in it — that is the point.

`Submission.lean` supplies the real definitions and proofs by importing `Monophilic`.

## What is in here

This file is meant to be read top to bottom.  Its nine sections follow the path the book's Part I
takes — colouring a graph, the chromatic polynomial, lists and choosability and monophilicity,
chordal graphs, Theorem 1, the machinery behind it, `2`-choosability, `2`-monophilicity, Donner —
and each section header says what the section is for.  A reader who is mathematically strong but
not a graph theorist should be able to follow it without the library.

**Results (`theorem_names` in `config.json`, 65 entries).** The keystones: the deletion and
disjoint-union identities, the chromatic polynomial and its evaluation, the three regimes of
monophilicity and the Erdős–Rubin–Taylor separation, Kirov–Naimi's Lemmas 1–6, Theorems 1 and 2,
Kostochka–Sidorenko, Dirac's lemma and Dirac's theorem, the `⟸` direction of Rubin's theorem, the
explicit threshold and Donner's theorem.

**Vocabulary (`definition_names` in `config.json`, 58 entries).** Exactly the terms those
statements mention, plus the handful of core notions the book defines on the way (`colorings`,
`IsProperColoring`, `IsNListAssignment`, `constList`, `colCounts`, `addPendantPair`):

* counting: `ListAssignment`, `IsNListAssignment`, `constList`, `IsProperColoring`, `colorings`,
  `col`, `colConst`, `colFix`, `Monophilic`, `Choosable`, `Minimizing`, `colCounts`,
  `listColorFunction`, `chromaticPolynomial`;
* constructions: `coneOn`, `addPendant`, `addPendantPair`, `delNone`, `inducedList`, `bridge`,
  `TowerV`, `TowerData`, `pendantTower`, `CliqueTowerData`, `cliqueTower`,
  `CliqueTowerData.IsSimplicial`, `IsChordal`, `IsSimplicialVertex`, `ERT.K`, `ERT.L₀`;
* paths, cycles and thetas: `PathV`, `pathG`, `pathStart`, `pathEnd`, `pathVtx`, `pathA`, `pathB`,
  `pathAssign`, `IsNNAssign`, `IsPathShape`, `closePath`, `ThetaV`, `theta`, `RubinFamily`;
* and sixteen `DecidableRel` / `Fintype` / `DecidableEq` instances (`instDecidableRelPathG`,
  `coneOn.instDecidableRel`, …).  These are not an editorial choice: `G.col L` does not typecheck
  without them, so they occur in the *types* of the listed theorems, and the comparator's traversal
  (`Comparator/Compare.lean`) requires every constant reachable from a listed type to be either a
  `definition_names` entry or bit-identical between challenge and solution — which a placeholder
  body is not.  With the present `theorem_names`, 52 library definitions are reachable and all 52
  must be listed; removing one (say `coneOn.instDecidableRel`) makes the comparator fail with
  `Const does not match between challenge and target`.

**What is deliberately not claimed.** The Part II machinery is *declared* here where the file needs
it to compile, but is not listed in `config.json`, because it is apparatus rather than content: the
bridge/swap apparatus beyond Lemma 2 itself (`colAvoid`, `swapRight`, `col_bridge`,
`col_swapRight_add`), the path-splitting isomorphism `pathSplitIso`, the rotation `rotIso` and the
cycle case-analysis it serves, the Whitney list-count internals (`listCount`, `compInter`,
`edgeGraph`, `compCount`, `col_eq_sum_powerset`), the conditional form of Dirac
(`HasSimplicialVertex`, `hasSimplicialVertex`, `monophilic_of_isChordal_of_dirac`) now that the
unconditional `monophilic_of_isChordal` is available, and degenerate or subsumed special cases
(`isChordal_bot`, `isChordal_of_isEmpty`, `IsChordal.of_embedding`, `IsChordal.deleteVertex`,
`isChordal_cliqueTower`, `monophilic_cliqueTower_of_isChordal`,
`two_le_col_closePath_of_not_const`, `listCount_eq_prod`, `listCount_constList`).

Lemma 3(b)(c) is the one place where a named result of the paper drags apparatus into the
vocabulary: its statement needs `IsNNAssign`, `IsPathShape`, `Minimizing` and `pathVtx`.  Following
the paper is worth those four entries, but this is a judgement call and easy to reverse — drop
`min_pathA_pathB_le_col` and `isPathShape_parity_of_minimizing` and all four fall out of the
closure by themselves.

The library's own internal helpers — `coneAdj`, `addPendantAdj`, `addPendantPairAdj`,
`pathSplitIsoAux`, `pathIdx`, `pathVtxEquiv`, `rotEquiv`, `pathSplitEquiv`, `pathGCongr`,
`optionSumEquiv`, `thetaBaseOf`, `thetaOf`, `lvl`, `levelAssign`, `thetaAssign`, `eraseEnds`,
`thetaWitness`, `optAssign`, `endPair`, `testM'`, `extendList`, `whitneySum`, `ConstOnEdge`,
`edgeDef`, `listInter`, `compFinset`, `compEdges`, `rhsL`, `univTowerData`, `topIsoTopOfEquiv`,
`towerVEquivFin`, `someEquivNeNone`, `coneOnInduceIso`, `coneOnDeleteIso`, `coneOnCongr`,
`neighborsAway`, `ReachIn`, `IsSimplicialIn`, the `#guard` fixtures `L1`, `L4`, `c4`, `c5`, … — are
omitted from the file entirely.

**Bodies.** Most definitions carry their **real bodies** rather than a placeholder, so the file
reads as a specification; the comparator never inspects the body of a `definition_names` entry.
Placeholders remain only where the body is not a statement: the graph constructions built as
`SimpleGraph` structure instances with tactic-proved `symm`/`loopless` fields (`coneOn`,
`addPendant`, `addPendantPair`, `bridge`), the two isomorphisms `pathSplitIso` and `rotIso`, and
the decidability instances.  Five bodies are forced rather than chosen: `ListAssignment` (its values
are applied as functions in other statements), `ThetaV`, `ERT.K` and `edgeGraph` (their `Fintype` /
`DecidableRel` instances are found by unfolding the abbreviation), and `HasSimplicialVertex` (a
universe-polymorphic `Prop` constant whose universe parameter lives only in its body).

## Where Lean fought the teaching order

Three places, each noted again in the section header concerned.  `ListAssignment` and `constList`
are declared in §1 although they belong to §3, because `col` is defined on a list assignment and
the palette count `colConst` is its special case.  `colFix` is declared in §1 although the book
introduces it with lists, because §1's deletion identity is stated with it.  And `monophilic_iso`
— isomorphism transfer, which belongs with §1's basics — is stated in §3, because the invariant
being transferred is monophilicity, which §3 defines.

Otherwise the order is the book's, including the chromatic polynomial at position 2 (it pulls
`compCount` and the `fromEdgeSet` decidability instance forward with it) and the Erdős–Rubin–Taylor
graph inside §3 as the example separating colourability from choosability.
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

/-! ### 1. Colouring a graph

A **proper colouring** gives adjacent vertices different colours; `col(G, L)` counts the proper
colourings drawn from a prescribed set of colours at each vertex, and `col(G, n)` is the special
case where every vertex may use the whole palette `{0, …, n-1}`.  Everything downstream is a
statement about these two counts.

Two orderings had to be traded off here.  The book introduces a single palette first and lists only
in §3, but the formalization defines `col` on a *list assignment* from the outset and recovers the
palette count as `colConst G n = col G (constList V n)`, so `ListAssignment` and `constList` have to
be declared before `col`; they are, immediately below, and their role is genuinely §3's.  Likewise
`colFix` (colourings that give a fixed colour to a fixed vertex) is stated here rather than in §3,
because the deletion identity `colFix_none_eq_col_delNone` — the recursion that drives the whole
development — needs it.  Isomorphism transfer belongs here too but is stated in §3, since the
invariant being transferred is monophilicity.
-/

section

universe u_2

/-- A **list assignment** for a graph on `V` gives each vertex a finite set of allowed colors. -/
abbrev ListAssignment (V : Type u_2) : Type u_2 := V → Finset ℕ

/-- The constant list assignment sending every vertex to `{0, 1, …, n-1}`; the paper's `[n]`. -/
def constList (V : Type u_2) (n : ℕ) : ListAssignment V := fun _ => range n

end

/-- `f` is a proper coloring of `G`: adjacent vertices get distinct colors. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) (f : V → ℕ) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w

/-- Not part of the specification: the decidability of `IsProperColoring`, needed only so that
`colorings` can be written as a `Finset.filter`.  Not listed in `config.json`. -/
instance instDecidableIsProperColoring {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Fintype V] (f : V → ℕ) : Decidable (G.IsProperColoring f) := by
  unfold IsProperColoring; infer_instance

/-- The finset of proper colorings of `G` drawn from the lists `L`. -/
def colorings {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : Finset (V → ℕ) :=
  (Fintype.piFinset L).filter G.IsProperColoring

/-- `col(G, L)`: the number of proper colorings of `G` from the list assignment `L`. -/
def col {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : ℕ := (G.colorings L).card

/-- `col(G, n)`: the number of proper colorings of `G` from the constant list `{0, …, n-1}`. -/
def colConst {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : ℕ := G.col (constList V n)

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

/-- `col(G, L, v, c)`: the number of colorings of `G` from `L` assigning color `c` to vertex `v`. -/
def colFix {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) (v : V) (c : ℕ) : ℕ :=
  ((G.colorings L).filter (fun f => f v = c)).card

/-- The graph obtained from `H` by deleting the vertex `none`. -/
abbrev delNone {V : Type*} (H : SimpleGraph (Option V)) : SimpleGraph V := H.comap some

instance instDecidableRelAdjDelNone {V : Type*} (H : SimpleGraph (Option V))
    [DecidableRel H.Adj] : DecidableRel H.delNone.Adj := sorry

/-- The list assignment induced on `H − none` by assigning the color `c` to `none`. -/
def inducedList {V : Type*} (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
    (M : ListAssignment (Option V)) (c : ℕ) : ListAssignment V :=
  fun v => if H.Adj none (some v) then (M (some v)).erase c else M (some v)

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

instance instDecidableRelSumAdjSum_monophilic {V W : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj] :
    DecidableRel (G ⊕g H).Adj := sorry

/-- **Colorings multiply over a disjoint union.** -/
theorem col_sum {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (M : ListAssignment (V ⊕ W)) :
    (G ⊕g H).col M = G.col (M ∘ Sum.inl) * H.col (M ∘ Sum.inr) := sorry

/-! ### 2. The chromatic polynomial

`col(G, n)` is a polynomial in `n`.  This section builds it by the Whitney subset expansion
`∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`, where `c(S)` counts the connected components of the spanning
subgraph with edge set `S`, and proves that evaluating it at `n` returns `col(G, n)`.  It sits here,
before lists are introduced, because it is a statement about the palette count alone — and because
§3's reformulation of monophilicity as `P_ℓ(G, n) = P(G, n)` needs it.
-/

/-- Adjacency in `fromEdgeSet S` is decidable when `S` comes from a `Finset` of edges. -/
instance decidableRelFromEdgeSetCoe {V : Type*} [DecidableEq V] (S : Finset (Sym2 V)) :
    DecidableRel (fromEdgeSet (S : Set (Sym2 V))).Adj := sorry

/-- `c(S)`: the number of connected components of the spanning subgraph of `V` whose edges are
exactly the non-loop elements of `S`. -/
def compCount {V : Type*} [Fintype V] [DecidableEq V] (S : Finset (Sym2 V)) : ℕ :=
  Fintype.card (fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent

/-- The **chromatic polynomial** of `G`, defined by the Whitney subset expansion
`∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`. -/
noncomputable def chromaticPolynomial {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Polynomial ℤ :=
  ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * Polynomial.X ^ compCount S

/-- **Evaluation of the chromatic polynomial counts colorings.** -/
theorem eval_chromaticPolynomial {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    (G.chromaticPolynomial).eval (n : ℤ) = (G.colConst n : ℤ) := sorry

/-- The chromatic polynomial of the edgeless graph is `X ^ |V|`. -/
theorem chromaticPolynomial_bot {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableRel (⊥ : SimpleGraph V).Adj] :
    chromaticPolynomial (⊥ : SimpleGraph V) = Polynomial.X ^ Fintype.card V := sorry

/-! ### 3. Lists instead of a palette

Now let each vertex carry its own list of `n` allowed colours.  `G` is **`n`-choosable** if every
such assignment admits a colouring at all, and **`n`-monophilic** if the constant assignment
*minimizes* the number of colourings — the paper's subject.  Equivalently, the list colour function
`P_ℓ(G, n)` (the minimum over all `n`-list assignments) agrees with the chromatic polynomial at `n`.

Three regimes: below `χ(G)` monophilicity is vacuous, above `χ_ℓ(G)` it is genuine, and in between
it fails.  That the middle regime is nonempty is not obvious, and the section closes with the
example that settles it: the Erdős–Rubin–Taylor graph `K_{n,nⁿ}`, which is `n`-colourable but not
`n`-choosable, witnessed by the explicit list assignment `L₀` admitting no colouring at all.
-/

/-- An **`n`-list assignment** gives every vertex a list of exactly `n` colors. -/
def IsNListAssignment {V : Type*} (L : ListAssignment V) (n : ℕ) : Prop := ∀ v, (L v).card = n

/-- `G` is **`n`-choosable** if it admits a coloring from every `n`-list assignment. -/
def Choosable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → 0 < G.col L

/-- `G` is **`n`-monophilic** when the number of list colorings is minimized by the constant list
assignment, among all assignments of lists of size `n`. -/
def Monophilic {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → G.colConst n ≤ G.col L

/-- **Monophilicity is an isomorphism invariant.** -/
theorem monophilic_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
    (e : G ≃g G') (n : ℕ) : G.Monophilic n ↔ G'.Monophilic n := sorry

/-- If `n < χ(G)` then `G` is `n`-monophilic, vacuously — there are no colorings at all from the
constant list. -/
theorem monophilic_of_not_colorable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : ℕ} (h : ¬ G.Colorable n) : G.Monophilic n := sorry

/-- If `χ(G) ≤ n < χ_ℓ(G)` then `G` is *not* `n`-monophilic. -/
theorem not_monophilic_of_colorable_of_not_choosable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
    (hcol : G.Colorable n) (hch : ¬ G.Choosable n) : ¬ G.Monophilic n := sorry

/-- The set of coloring counts achievable by `n`-list assignments. -/
def colCounts {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Set ℕ := {c | ∃ L : ListAssignment V, IsNListAssignment L n ∧ G.col L = c}

/-- **The list color function** `P_ℓ(G, n)`: the least number of colorings achievable by any
`n`-list assignment. -/
noncomputable def listColorFunction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) : ℕ := sInf (G.colCounts n)

/-- **`n`-monophilicity is exactly `P_ℓ(G, n) = P(G, n)`.** -/
theorem monophilic_iff_listColorFunction_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.Monophilic n ↔ G.listColorFunction n = G.colConst n := sorry

/-- **`P_ℓ(G, n) = P(G, n)` with a genuine polynomial on the right.** -/
theorem monophilic_iff_listColorFunction_eq_eval {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.Monophilic n ↔ (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) := sorry

end SimpleGraph

namespace SimpleGraph.ERT

/-- Adjacency in a complete bipartite graph is decidable. -/
instance instDecidableRelCompleteBipartiteAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj := sorry

/-- `K_{n,nⁿ}`, the complete bipartite graph whose right side is indexed by the functions
`Fin n → Fin n`. -/
abbrev K (n : ℕ) : SimpleGraph (Fin n ⊕ (Fin n → Fin n)) :=
  completeBipartiteGraph (Fin n) (Fin n → Fin n)

/-- The Erdős–Rubin–Taylor list assignment on `K_{n,nⁿ}`, called `L₀` in Kirov–Naimi §5. -/
def L₀ (n : ℕ) : ListAssignment (Fin n ⊕ (Fin n → Fin n)) :=
  Sum.elim (fun i => (univ : Finset (Fin n)).image fun j : Fin n => i.val * n + j.val)
    (fun φ => (univ : Finset (Fin n)).image fun i : Fin n => i.val * n + (φ i).val)

/-- **The key computation**: `col(K_{n,nⁿ}, L₀) = 0`, i.e. `L₀` admits no proper coloring at all. -/
theorem col_L₀_eq_zero (n : ℕ) : (K n).col (L₀ n) = 0 := sorry

/-- `K_{n,nⁿ}` is **not** `n`-choosable, witnessed by `L₀`. -/
theorem not_choosable (n : ℕ) : ¬ (K n).Choosable n := sorry

/-- `K_{n,nⁿ}` is `n`-colorable once `2 ≤ n`.  Together with `not_choosable` this is the
Erdős–Rubin–Taylor separation: `χ(K_{n,nⁿ}) ≤ n < χ_ℓ(K_{n,nⁿ})`. -/
theorem colorable (n : ℕ) (hn : 2 ≤ n) : (K n).Colorable n := sorry

/-- Since `K_{n,nⁿ}` is `n`-colorable but not `n`-choosable, it is not `n`-monophilic. -/
theorem not_monophilic (n : ℕ) (hn : 2 ≤ n) : ¬ (K n).Monophilic n := sorry

end SimpleGraph.ERT

namespace SimpleGraph

/-! ### 4. Chordal graphs and Kostochka–Sidorenko

The first positive result.  Adding a vertex joined to a *clique* preserves `n`-monophilicity
(Kirov–Naimi's Lemma 1), so any graph built from nothing by repeated such attachments — a
*simplicial elimination ordering*, read backwards — is `n`-monophilic for every `n`.  Dirac's
theorem identifies those graphs as exactly the **chordal** ones (every cycle of length `≥ 4` has a
chord), and is proved here rather than assumed, so the conclusion
`monophilic_of_isChordal` is unconditional.
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

section

universe u

/-- The vertex type of `G` after `k` successive pendant attachments: `V` with `k` extra points. -/
def TowerV (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => Option (TowerV V k)

instance instDecidableEqTowerV {V : Type u} [DecidableEq V] : (k : ℕ) → DecidableEq (TowerV V k) :=
  sorry

instance instFintypeTowerV {V : Type u} [Fintype V] : (k : ℕ) → Fintype (TowerV V k) := sorry

/-- The data specifying a tower of `k` cone attachments over `V`: at each stage, the finset of
already-existing vertices that the new vertex is joined to. -/
def CliqueTowerData (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => CliqueTowerData V k × Finset (TowerV V k)

/-- **A tower of cone attachments.** `cliqueTower G k d` is the graph obtained from `G` by adding
`k` new vertices one after another, the `i`-th of them joined to the set recorded in `d`. -/
def cliqueTower {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → CliqueTowerData V k → SimpleGraph (TowerV V k)
  | 0, _ => G
  | k + 1, d => coneOn (cliqueTower G k d.1) d.2

/-- Adjacency in a clique tower is decidable, by recursion on the height of the tower. -/
instance instDecidableRelCliqueTower {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] :
    (k : ℕ) → (d : CliqueTowerData V k) → DecidableRel (cliqueTower G k d).Adj := sorry

/-- **The simplicial condition.** `d.IsSimplicial` says that at every stage of the tower the set of
old vertices to which the new vertex is attached is a clique *of the graph existing at that
stage*. -/
def CliqueTowerData.IsSimplicial {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → CliqueTowerData V k → Prop
  | 0, _ => True
  | k + 1, d =>
      (cliqueTower G k d.1).IsClique ((d.2 : Finset (TowerV V k)) : Set (TowerV V k)) ∧
        CliqueTowerData.IsSimplicial G k d.1

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

end

/-- **A chordal graph.** Every cycle of length at least `4` has a chord: an edge of the graph
joining two vertices of the cycle which is not itself an edge of the cycle.  Phrased through
Mathlib's `SimpleGraph.Walk.IsChordless`. -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ {u : V} (c : G.Walk u u), c.IsCycle → 4 ≤ c.length → ¬ c.IsChordless

/-- **A simplicial vertex** is one whose neighbourhood is a clique.  Deleting a simplicial vertex
is the inverse of the cone construction `SimpleGraph.coneOn`. -/
def IsSimplicialVertex {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

/-- `G` with the vertex `v` deleted: the subgraph induced on the vertices other than `v`. -/
abbrev deleteVertex {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph {x : V // x ≠ v} :=
  G.comap (Function.Embedding.subtype fun x => x ≠ v)

/-- **Complete graphs are chordal.** -/
theorem isChordal_top {V : Type*} : (⊤ : SimpleGraph V).IsChordal := sorry

/-- The empty graph is chordal: it has no cycles. -/
theorem isChordal_bot {V : Type*} : (⊥ : SimpleGraph V).IsChordal := sorry

/-- A graph with no vertices at all is chordal. -/
theorem isChordal_of_isEmpty {V : Type*} [IsEmpty V] (G : SimpleGraph V) : G.IsChordal := sorry

/-- **Chordality passes to subgraphs presented by an embedding.** -/
theorem IsChordal.of_embedding {V : Type*} {G : SimpleGraph V} {W : Type*} {G' : SimpleGraph W}
    (f : G' ↪g G) (h : G.IsChordal) : G'.IsChordal := sorry

/-- **Chordality is an isomorphism invariant.** -/
theorem IsChordal.of_iso {V : Type*} {G : SimpleGraph V} {W : Type*} {G' : SimpleGraph W}
    (e : G' ≃g G) (h : G.IsChordal) : G'.IsChordal := sorry

/-- **Chordality passes to induced subgraphs.** -/
theorem IsChordal.induce {V : Type*} {G : SimpleGraph V} (s : Set V) (h : G.IsChordal) :
    (G.induce s).IsChordal := sorry

/-- **Coning off a clique preserves chordality.** This is the chordal-graph counterpart of
Kirov–Naimi's Lemma 1 (`SimpleGraph.Monophilic.coneOn`). -/
theorem IsChordal.coneOn {V : Type*} {G : SimpleGraph V} {K : Finset V} (hG : G.IsChordal)
    (hK : G.IsClique (K : Set V)) : (coneOn G K).IsChordal := sorry

/-- Deleting a vertex from a chordal graph leaves a chordal graph. -/
theorem IsChordal.deleteVertex {V : Type*} {G : SimpleGraph V} (h : G.IsChordal) (v : V) :
    (G.deleteVertex v).IsChordal := sorry

/-- **A simplicial clique tower builds a chordal graph.** -/
theorem isChordal_cliqueTower {V : Type*} (G : SimpleGraph V) (hG : G.IsChordal) :
    ∀ (k : ℕ) (d : CliqueTowerData V k), CliqueTowerData.IsSimplicial G k d →
      (cliqueTower G k d).IsChordal := sorry

/-- **Dirac's lemma.** A chordal graph on a nonempty finite vertex type has a simplicial vertex.
This is the graph-theoretic input that Kirov–Naimi leave implicit. -/
theorem exists_isSimplicialVertex {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    [Nonempty V] (hG : G.IsChordal) : ∃ v, G.IsSimplicialVertex v := sorry

/-- **The four-cycle is not chordal.** -/
theorem not_isChordal_cycleGraph_four : ¬ (cycleGraph 4).IsChordal := sorry

/-- **The five-cycle is not chordal.** -/
theorem not_isChordal_cycleGraph_five : ¬ (cycleGraph 5).IsChordal := sorry

section

universe u

/-- **Dirac's lemma**, as a named statement: every chordal graph on a nonempty finite vertex type
has a simplicial vertex.  Stated separately so that the one graph-theoretic input of the induction
below is visible in the signature of `SimpleGraph.monophilic_of_isChordal_of_dirac`; it is then
discharged by `SimpleGraph.hasSimplicialVertex`. -/
def HasSimplicialVertex : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), Nonempty V → G.IsChordal →
    ∃ v : V, G.IsSimplicialVertex v

/-- **Dirac's lemma**, discharging the hypothesis `SimpleGraph.HasSimplicialVertex`. -/
theorem hasSimplicialVertex : HasSimplicialVertex.{u} := sorry

/-- The Kostochka–Sidorenko theorem *relative to* Dirac's lemma: a chordal graph is
`n`-monophilic for every `n`, given `hD`.  The induction is on the number of vertices, peeling off
a simplicial vertex and putting it back with Kirov–Naimi's Lemma 1. -/
theorem monophilic_of_isChordal_of_dirac (hD : HasSimplicialVertex.{u}) {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) :
    G.Monophilic n := sorry

/-- **The Kostochka–Sidorenko theorem, under its own name and unconditionally.** *Every chordal
graph is `n`-monophilic, for every `n`.*

This is the statement the tower form `SimpleGraph.monophilic_cliqueTower_of_isEmpty` could only
approximate, because "chordal" was undefined there.  The missing link is Dirac's lemma
(`SimpleGraph.exists_isSimplicialVertex`), now proved, so there is no hypothesis left to borrow. -/
theorem monophilic_of_isChordal {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) : G.Monophilic n := sorry

/-- **The easy direction of Dirac's theorem.** A graph presented by a simplicial elimination
ordering — built from nothing by successively attaching a vertex to a clique of the graph built so
far — is chordal. -/
theorem isChordal_cliqueTower_of_isEmpty {V : Type u} [IsEmpty V] (G : SimpleGraph V) (k : ℕ)
    (d : CliqueTowerData V k) (hd : CliqueTowerData.IsSimplicial G k d) :
    (cliqueTower G k d).IsChordal := sorry

/-- **Dirac's theorem, easy direction, restated for `n`-monophilicity**: the two routes to the
Kostochka–Sidorenko theorem agree. -/
theorem monophilic_cliqueTower_of_isChordal {V : Type u} [Fintype V] [DecidableEq V] [IsEmpty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n k : ℕ) (d : CliqueTowerData V k)
    (hd : CliqueTowerData.IsSimplicial G k d) : (cliqueTower G k d).Monophilic n := sorry

/-- **Dirac's theorem, hard direction.** A chordal graph on `m` vertices is isomorphic to the graph
built from nothing by `m` cone attachments, each over a clique of the graph built so far: peeling
off a simplicial vertex at each step reads off a simplicial elimination ordering. -/
theorem exists_cliqueTower_of_isChordal :
    ∀ (m : ℕ) {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = m → G.IsChordal →
        ∃ d : CliqueTowerData (Fin 0) m,
          CliqueTowerData.IsSimplicial (⊥ : SimpleGraph (Fin 0)) m d ∧
            Nonempty (G ≃g cliqueTower (⊥ : SimpleGraph (Fin 0)) m d) := sorry

/-- **Dirac's theorem.** *A finite graph is chordal if and only if it has a simplicial elimination
ordering*, presented backwards and constructively as a `SimpleGraph.cliqueTower` over the empty
graph. -/
theorem isChordal_iff_exists_cliqueTower {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsChordal ↔ ∃ (k : ℕ) (d : CliqueTowerData (Fin 0) k),
      CliqueTowerData.IsSimplicial (⊥ : SimpleGraph (Fin 0)) k d ∧
        Nonempty (G ≃g cliqueTower (⊥ : SimpleGraph (Fin 0)) k d) := sorry

end

/-! ### 5. Theorem 1: every cycle is `n`-monophilic

The paper's main theorem.  A path is built by repeatedly attaching a pendant vertex, and a cycle is
a path with its two ends joined.  On a path, the `(n, n-1)`-list assignments come in two shapes,
counted by the mutually recursive `A_k` and `B_k`; the cycle count `col(C, n) = n · A_{k-1}` follows,
and the closed form `(n-1)^v + (-1)^v (n-1)` drops out.  The statements are collected here; the
apparatus that proves them is §6.
-/

/-- `G` with one new pendant vertex `none`, attached to `v`. -/
def addPendant {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) := sorry

instance instDecidableRelOptionAdjAddPendant {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : DecidableRel (G.addPendant v).Adj := sorry

/-- `G` with one new vertex `none`, joined to both `u` and `v`. -/
def addPendantPair {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) := sorry

instance instDecidableRelAddPendantPair {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (u v : V) : DecidableRel (G.addPendantPair u v).Adj := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- The vertex type of a path of length `k` (so `k + 1` vertices). -/
def PathV : ℕ → Type
  | 0 => Unit
  | k + 1 => Option (PathV k)

instance instDecidableEqPathV : (k : ℕ) → DecidableEq (PathV k) := sorry

instance instFintypePathV : (k : ℕ) → Fintype (PathV k) := sorry

/-- The terminal vertex of `pathG k` that was attached last. -/
def pathEnd : (k : ℕ) → PathV k
  | 0 => ()
  | _ + 1 => none

/-- The other terminal vertex of `pathG k`. -/
def pathStart : (k : ℕ) → PathV k
  | 0 => ()
  | k + 1 => some (pathStart k)

/-- The path of length `k`: `k + 1` vertices in a row. -/
def pathG : (k : ℕ) → SimpleGraph (PathV k)
  | 0 => ⊥
  | k + 1 => (pathG k).addPendant (pathEnd k)

instance instDecidableRelPathG : (k : ℕ) → DecidableRel (pathG k).Adj := sorry

mutual

/-- Paper's `A_k` for `n = m + 2`: the number of colorings of a path of length `k` coming from a
type A list assignment.  `A_0 = m + 1` and `A_{k+1} = (m + 1) * B_k`. -/
def pathA (m : ℕ) : ℕ → ℕ
  | 0 => m + 1
  | k + 1 => (m + 1) * pathB m k

/-- Paper's `B_k` for `n = m + 2`: the number of colorings of a path of length `k` coming from a
type B list assignment.  `B_0 = m` and `B_{k+1} = A_k + m * B_k`. -/
def pathB (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => pathA m k + m * pathB m k

end

/-- Equation (5) of the paper: `A_k - B_k = (-1) ^ k`, as an identity in `ℤ`. -/
theorem pathA_sub_pathB (m k : ℕ) : ((pathA m k : ℤ) - (pathB m k : ℤ)) = (-1) ^ k := sorry

/-- Closed form for `A_k`, cleared of the division:
`(m + 2) * A_k = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k)`. -/
theorem pathA_closed_form (m k : ℕ) :
    ((m + 2) * pathA m k : ℤ) = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k) := sorry

/-- The `(n, n-1)`-list assignment on the path of length `k` missing color `x` at `pathEnd` and
color `y` at `pathStart`; type A when `x = y`, type B otherwise. -/
def pathInterior : (k : ℕ) → (n y : ℕ) → ListAssignment (PathV k)
  | 0, n, y => fun _ => (range n).erase y
  | k + 1, n, y => fun v =>
      match v with
      | none => range n
      | some w => pathInterior k n y w

def pathAssign : (k : ℕ) → (n x y : ℕ) → ListAssignment (PathV k)
  | 0, n, x, y => fun _ => ((range n).erase x).erase y
  | k + 1, n, x, y => fun v =>
      match v with
      | none => (range n).erase x
      | some w => pathInterior k n y w

/-- **Lemma 3(a), graph side.** The number of colorings of a path of length `k` from an
`(n, n-1)`-list assignment is `A_k` if the assignment is type A and `B_k` if it is type B. -/
theorem col_pathAssign (m : ℕ) :
    ∀ (k x y : ℕ), x < m + 2 → y < m + 2 →
      (pathG k).col (pathAssign k (m + 2) x y) = if x = y then pathA m k else pathB m k := sorry

/-- The path of length `k` closed up: `pathG k` together with one extra edge joining its two
terminal vertices.  For `k ≥ 2` this is the cycle on `k + 1` vertices. -/
def closePath : (k : ℕ) → SimpleGraph (PathV k)
  | 0 => ⊥
  | k + 1 => (pathG k).addPendantPair (pathEnd k) (pathStart k)

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
def reach (k : ℕ) (L : ListAssignment (PathV k)) (c : ℕ) : Finset ℕ :=
  (((pathG k).colorings L).filter (fun f => f (pathEnd k) = c)).image (fun f => f (pathStart k))

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

/-! ### 6. The machinery behind Theorem 1

Three technical steps, separated out because they are means rather than ends.  Lemma 2: cutting a
graph along a **bridge** and swapping colours on one side does not increase the count, so the lists
at the two ends may be assumed nested.  Lemma 4: on a path, enlarging the lists *strictly* increases
the count.  Lemma 3(b)(c): every `(n, n-1)`-assignment on a path admits at least `min(A_k, B_k)`
colourings, and a *minimizing* one has the shape dictated by the parity of `k`.
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
    (L : ListAssignment V) (v : V) (c : ℕ) : ℕ :=
  ((G.colorings L).filter fun f => f v ≠ c).card

/-- `swapRight M c₁ c₂` agrees with `M` on the left-hand side and applies the transposition
`Equiv.swap c₁ c₂` to every list on the right-hand side. -/
def swapRight {V W : Type*} (M : ListAssignment (V ⊕ W)) (c₁ c₂ : ℕ) : ListAssignment (V ⊕ W) :=
  Sum.elim (fun v => M (.inl v)) (fun w => (M (.inr w)).image (Equiv.swap c₁ c₂))

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

/-- `L` is **minimizing** for `G` when no list assignment with the same list sizes admits fewer
colorings. -/
def Minimizing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V) : Prop :=
  ∀ L' : ListAssignment V, (∀ v, (L' v).card = (L v).card) → G.col L ≤ G.col L'

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- **Lemma 4 of Kirov–Naimi.** For a path, enlarging the lists *strictly* increases the number of
colorings, provided the larger assignment gives at least two colors to every vertex. -/
theorem col_lt_col_of_ssubset (k : ℕ) {L L' : ListAssignment (PathV k)}
    (hsub : ∀ v, L v ⊆ L' v) (hne : L ≠ L') (hcard : ∀ v, 2 ≤ (L' v).card) :
    (pathG k).col L < (pathG k).col L' := sorry

/-- **Cutting a path at an edge.** Deleting the edge between the vertices numbered `a` and `a + 1`
of the path of length `a + b + 1` exhibits it as
`bridge (pathG a) (pathG b) (pathStart a) (pathEnd b)`. -/
def pathSplitIso (a b : ℕ) :
    pathG (a + b + 1) ≃g bridge (pathG a) (pathG b) (pathStart a) (pathEnd b) := sorry

/-- The vertex numbered `i` of the path of length `k`, counting from `pathEnd k` (number `0`)
towards `pathStart k` (number `k`). -/
def pathVtx : (k : ℕ) → ℕ → PathV k
  | 0, _ => ()
  | _ + 1, 0 => none
  | k + 1, i + 1 => some (pathVtx k i)

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

namespace SimpleGraph

/-! ### 7. `2`-choosability: Rubin's list

Which graphs are `2`-choosable?  Choosability is inherited by subgraphs, and — the key reduction —
is unchanged by attaching or removing pendant vertices, so a connected graph may be replaced by its
**core**.  Rubin's theorem says the `2`-choosable cores are exactly a single vertex, an even cycle,
and the theta graphs `θ_{2,2,2m}`.  The `⟸` direction is proved here; the `⟹` direction is the one
piece of the story that no proof assistant has, and §8 borrows it explicitly.

The monophilic core reduction (Kirov–Naimi's Lemma 5) is stated alongside its choosability twin,
since both are properties of the same `pendantTower` construction.
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

section

universe u

/-- The data specifying a tower of `k` pendant attachments: for each step, the already-existing
vertex at which the new pendant vertex is attached. -/
def TowerData (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => TowerData V k × TowerV V k

end

/-- **A tower of pendant attachments.** `pendantTower G k d` is the graph obtained from `G` by
attaching `k` pendant vertices one after another. -/
def pendantTower {V : Type*} (G : SimpleGraph V) :
    (k : ℕ) → TowerData V k → SimpleGraph (TowerV V k)
  | 0, _ => G
  | k + 1, d => (pendantTower G k d.1).addPendant d.2

section

universe u

instance instDecidableRelPendantTower {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] :
    (k : ℕ) → (d : TowerData V k) → DecidableRel (pendantTower G k d).Adj := sorry

end

/-- The pendant step for `SimpleGraph.addPendant`. -/
theorem monophilic_addPendant_iff {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (v : V) (n : ℕ) :
    (G.addPendant v).Monophilic n ↔ G.Monophilic n := sorry

/-- **Kirov–Naimi, Lemma 5.** A graph built from `G` by any finite sequence of pendant attachments
is `n`-monophilic if and only if `G` is; equivalently, a graph is `n`-monophilic iff its core is. -/
theorem monophilic_pendantTower_iff {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (n : ℕ) :
    ∀ (k : ℕ) (d : TowerData V k), (pendantTower G k d).Monophilic n ↔ G.Monophilic n := sorry

/-- **The core reduction for choosability.** For `2 ≤ n`, pendant attachments do not change
`n`-choosability.  This mirrors `SimpleGraph.monophilic_pendantTower_iff`. -/
theorem choosable_pendantTower_iff {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n : ℕ} (hn : 2 ≤ n) :
    ∀ (k : ℕ) (d : TowerData V k), (pendantTower G k d).Choosable n ↔ G.Choosable n := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

/-- The vertex type of `θ_{2,2,2m}`. -/
abbrev ThetaV (m : ℕ) : Type := Option (Option (PathV (2 * m)))

/-- The theta graph `θ_{2,2,2m}`. -/
def theta (m : ℕ) : SimpleGraph (ThetaV m) :=
  coneOn (coneOn (pathG (2 * m)) {pathStart (2 * m), pathEnd (2 * m)})
    {some (pathStart (2 * m)), some (pathEnd (2 * m))}

instance instDecidableRelTheta (m : ℕ) : DecidableRel (theta m).Adj := sorry

/-- **`θ_{2,2,2m}` is `2`-choosable, for every `m ≥ 1`.** -/
theorem choosable_theta (m : ℕ) (hm : 1 ≤ m) : (theta m).Choosable 2 := sorry

/-- **An even cycle is `2`-choosable**, as a corollary of Theorem 1. -/
theorem choosable_two_closePath_of_odd {k : ℕ} (hk : Odd k) (hk2 : 2 ≤ k) :
    (closePath k).Choosable 2 := sorry

/-- **An odd cycle is not `2`-choosable.** -/
theorem not_choosable_two_closePath_of_even {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    ¬ (closePath k).Choosable 2 := sorry

/-- A graph is on **Rubin's list** when it is a single vertex, an even cycle, or `θ_{2,2,2m}`,
stated up to isomorphism. -/
def RubinFamily {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Subsingleton V ∨
  (∃ k, Odd k ∧ 2 ≤ k ∧ Nonempty (G ≃g closePath k)) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (G ≃g theta m))

/-- **Rubin's theorem, ⟸ direction: every graph on Rubin's list is `2`-choosable.** -/
theorem choosable_two_of_rubinFamily {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : RubinFamily G) : G.Choosable 2 := sorry

end Monophilic

namespace SimpleGraph

/-! ### 8. `2`-monophilicity: Theorem 2

The classification.  `K₂,₃ = θ_{2,2,2}` is `2`-monophilic (Lemma 6) while `θ_{2,2,2m}` is not for
`m ≥ 2`, and those two facts, plus §5's cycles and §4's trees, turn Rubin's list into a list of the
`2`-monophilic graphs: a connected graph is `2`-monophilic exactly when it is not `2`-colourable or
its core is a vertex, an even cycle, or `K₂,₃`.  Rubin's theorem enters as an explicit hypothesis,
with the three alternatives kept abstract so that the loan is visible in the signature.
-/

/-- Adjacency in a complete bipartite graph is decidable. -/
instance instDecidableRelCompleteBipartiteGraphAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj := sorry

/-- **Lemma 6 of Kirov–Naimi.** `K₂,₃` is `2`-monophilic. -/
theorem monophilic_K23 : (completeBipartiteGraph (Fin 2) (Fin 3)).Monophilic 2 := sorry

end SimpleGraph

namespace Monophilic

open SimpleGraph

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

/-! ### 9. Every graph, eventually

Donner's theorem: *every* graph is `n`-monophilic once `n` is large enough.  The proof given here is
an inclusion–exclusion argument that also yields an explicit threshold — `n > 2^{|E(G)|}` suffices —
by running the Whitney expansion of §2 for an arbitrary list assignment rather than a single
palette.
-/

/-- The spanning subgraph of `V` with edge set `S` (loops in `S` are discarded). -/
abbrev edgeGraph {V : Type*} (S : Finset (Sym2 V)) : SimpleGraph V :=
  fromEdgeSet (S : Set (Sym2 V))

/-- `⋂_{v ∈ C} L v` for a connected component `C` of `edgeGraph S`. -/
def compInter {V : Type*} [Fintype V] [DecidableEq V] (L : ListAssignment V)
    (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) : Finset ℕ :=
  let U : Finset V := Finset.univ.filter (fun v => v ∈ C.supp)
  {a ∈ U.biUnion L | ∀ v ∈ U, a ∈ L v}

/-- The number of colorings of `V` from the lists `L` that are constant on every edge of `S`. -/
def listCount {V : Type*} [Fintype V] [DecidableEq V] (L : ListAssignment V)
    (S : Finset (Sym2 V)) : ℕ :=
  #{f ∈ Fintype.piFinset L | ∀ e ∈ S, (Sym2.map f e).IsDiag}

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
