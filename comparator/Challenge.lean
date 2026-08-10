import Mathlib
/-!
# List coloring and enumerative chromatic-choosability — the challenge statements

This file is the *statement surface* of the `graph_coloring` development, a formalization of

> Radoslav Kirov and Ramin Naimi, *List coloring and `n`-monophilic graphs*,
> Ars Combinatoria (arXiv:1004.5183),

together with the chromatic-polynomial / list-color-function reformulation, Dirac's theorem,
Rubin's theorem and Donner's theorem.  Every declaration below is stated exactly as in the library;
the theorems are left with a placeholder proof, so that the comparator can check a submission's
statements against these.  Compiling this file is *expected* to report "declaration uses `sorry`" —
that is the point.

`Submission.lean` supplies the real definitions and proofs by importing `ListColoring`.

## What is claimed

Ten theorems.  They are the load-bearing ones — the named results a reader would quote — and
nothing else is claimed here:

1. `eval_chromaticPolynomial` — the chromatic polynomial evaluates to the colouring count
2. `ecc_iff_listColorFunction_eq_eval` — `P_ℓ(G, n) = P(G, n)` *is* enumerative
   chromatic-choosability at `n`
3. `ERT.not_choosable` and 4. `ERT.colorable` — `K_{n,nⁿ}` is `n`-colourable but not `n`-choosable,
   so the middle regime `χ(G) ≤ n < χ_ℓ(G)` is nonempty (Erdős–Rubin–Taylor)
5. `ecc_of_isChordal` — **Kostochka–Sidorenko**: every chordal graph is enumeratively
   chromatic-choosable at `n`
6. `isChordal_iff_exists_cliqueTower` — **Dirac**: chordal ⟺ a simplicial elimination ordering
7. `ecc_closePath_of_two_le` — **Kirov–Naimi, Theorem 1**: every cycle is enumeratively
   chromatic-choosable at `n`
8. `rubinTheorem` — **Rubin**: the `2`-choosable connected graphs, classified by their core
9. `ecc_two_iff` — **Kirov–Naimi, Theorem 2**, with no hypothesis beyond connectivity
10. `exists_ecc_forall_ge` — **Donner**: every graph is enumeratively chromatic-choosable at `n` for
    large `n`

`ERT.colorable` is the tenth; on its own `not_choosable` says only that `χ_ℓ > n`, and the point of
the example is the *separation*.

Claims 8 and 9 replace the two weaker ones this file used to carry.  Rubin's theorem is now proved
in the library rather than borrowed, so `ListColoring.choosable_two_of_rubinFamily` (its `⟸` half,
all that was provable before) is subsumed by claim 8, and `SimpleGraph.ecc_two_iff_of_rubin_hard`
(Theorem 2 with Rubin's `⟹` as a hypothesis and the core alternatives left as abstract `Prop`s) is
superseded by claim 9: it understated what is proved, and abstract `CoreIsVertex`/`CoreIsTheta`
variables say nothing about cores, so certifying it certified less than the library has.  Both are
still in the library, in `ListColoring/Rubin.lean`, as a record of the shape of the loan that was
outstanding; neither is claimed here.  `RubinFamily`, which this file carried only in order to state
the first of them, is deleted rather than delisted.

## What is defined

`definition_names` is exactly what those ten statements need, computed rather than curated: the 22
definitions reachable from their types, plus the 24 notions those 22 are written in terms of, so
that the file can be read without the library.  No definition is here for any other reason; in
particular only six are `Fintype`/`DecidableEq`/`DecidableRel` instances.  Four of the six occur in
the *type* of a listed theorem — `(closePath k).ECCAt (m + 2)` does not typecheck without them — and
the other two, `instDecidableRelPathG` and `instDecidableRelTheta`, are what `CoreIsVertex` and
`CoreIsK23` need in order to name `pathG 0` and `theta 1` as graphs at all.

Most definitions carry their **real bodies**, so the file reads as a specification; the comparator
never inspects the body of a `definition_names` entry.  Placeholders remain only where the body is
not a statement: the graph constructions built as `SimpleGraph` structure instances with
tactic-proved `symm`/`loopless` fields (`coneOn`, `addPendant`, `addPendantPair`), and the
decidability instances — the six listed ones, and `decidableRelFromEdgeSetCoe` below.  Ten
declarations in all, so this file's twenty `sorry`s are ten theorems and ten placeholders.  Two
bodies are forced rather than chosen — `ListAssignment`, whose values
are applied as functions in other statements, and `ThetaV`, whose instances are found by unfolding
the abbreviation.  Two declarations appear without being listed, because a *body* rather than a
statement needs them: `instDecidableIsProperColoring` (so `colorings` can be a `Finset.filter`) and
`decidableRelFromEdgeSetCoe` (so `compCount` can count components).

One body is load-bearing in a way no other is.  `rubinTheorem`'s type is the bare constant
`RubinTheorem`, so **the statement of Rubin's theorem is the body of `RubinTheorem`** — unfolding it
is the only way to see what claim 8 says.  That body is therefore reproduced verbatim, and the
library is where it is checked: the comparator matches `RubinTheorem` by type, which is `Prop`.

## How to read it

The nine sections follow the path the book's Part I takes.  Sections that no longer carry a claim
still carry the story: §1 introduces the vocabulary the rest is written in, and §6 is prose only,
pointing at the machinery in the library.  Everything the library proves and this file does not
claim — Kirov–Naimi's Lemmas 1–6, the three regimes, the explicit threshold `n > 2^{|E|}`, Dirac's
lemma, the chromatic polynomial of a cycle in closed form, the `2`-choosable generalized theta
graphs of arbitrary arity (`ListColoring.choosable_two_gtheta_iff`) — is still there, under the
names given in the section headers below.  The last of those was weighed as an eleventh claim and
left out on this file's own rule: its statement is written in `ListColoring.ValidArms` and
`ListColoring.GoodArms`, a *normalization convention* on the list of arm lengths (sorted, at most
one arm of length one) rather than mathematics, and a keystone should not drag a proof's
bookkeeping into the certified surface.

Three places where Lean fought the teaching order.  `ListAssignment` and `constList` are declared in
§1 although they belong to §3, because `col` is defined on a list assignment and the palette count
`colConst` is its special case.  The chromatic polynomial sits at §2, before lists, which pulls
`compCount` and the `fromEdgeSet` decidability instance forward with it.  And `TowerData` and
`pendantTower` — the core reduction that §7 and §8 are stated with — are declared in §5 beside
`addPendant`, because iterated `addPendant` is all they are.
-/

open Finset

namespace SimpleGraph

/-! ### 1. Colouring a graph

A **proper colouring** gives adjacent vertices different colours.  `col(G, L)` counts the proper
colourings that draw each vertex's colour from a prescribed finite list `L v`, and `col(G, n)` is
the special case where every vertex may use the whole palette `{0, …, n-1}`.  Every claim in this
file is ultimately a statement about those two counts.

The library proves the basic identities here — colour renaming (`col_image_of_injOn`), the bridge
to Mathlib's `Colorable` (`colConst_pos_iff_colorable`), the deletion recursion
(`col_eq_sum_delNone`, `colFix_none_eq_col_delNone`, with `colFix`, `delNone` and `inducedList`),
and multiplicativity over disjoint unions (`col_sum`).  None of them is claimed here; this section
exists to define the vocabulary the ten theorems are written in.
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

/-! ### 2. The chromatic polynomial

`col(G, n)` is a polynomial in `n`.  It is built here by the Whitney subset expansion
`∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`, where `c(S)` counts the connected components of the spanning
subgraph with edge set `S`, and the first claim is that evaluating it at `n` returns `col(G, n)`.

It sits before lists are introduced because it is a statement about the palette count alone — and
because §3's reformulation of enumerative chromatic-choosability needs it.
`SimpleGraph.chromaticPolynomial_bot` (`P(⊥, X) = X^{|V|}`) is in the library. -/

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

/-! ### 3. Lists instead of a palette

Now let each vertex carry its own list of `n` allowed colours. `G` is **`n`-choosable** if every
such assignment admits a colouring at all, and **enumeratively chromatic-choosable at `n`** if the
constant assignment *minimizes* the number of colourings — the paper's subject. The list colour
function `P_ℓ(G, n)` is that minimum, and the second claim is that enumerative
chromatic-choosability at `n` is exactly `P_ℓ(G, n) = P(G, n)`.

Three regimes: below `χ(G)` enumerative chromatic-choosability holds vacuously, above `χ_ℓ(G)` it is genuine, and in
between it fails (`ecc_of_not_colorable`, `not_ecc_of_colorable_of_not_choosable` in
the library).  That the middle regime is nonempty is the Erdős–Rubin–Taylor example, claimed here:
`K_{n,nⁿ}` is `n`-colourable but not `n`-choosable.  The witness — an explicit list assignment
`ERT.L₀` admitting no colouring at all, `ERT.col_L₀_eq_zero` — is in the library.
-/

/-- An **`n`-list assignment** gives every vertex a list of exactly `n` colors. -/
def IsNListAssignment {V : Type*} (L : ListAssignment V) (n : ℕ) : Prop := ∀ v, (L v).card = n

/-- `G` is **`n`-choosable** if it admits a coloring from every `n`-list assignment. -/
def Choosable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → 0 < G.col L

/-- `G` is **enumeratively chromatic-choosable at `n`** when the number of list colorings is
minimized by the constant list assignment, among all assignments of lists of size `n`. -/
def ECCAt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Prop :=
  ∀ L : ListAssignment V, IsNListAssignment L n → G.colConst n ≤ G.col L

/-- The set of coloring counts achievable by `n`-list assignments. -/
def colCounts {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : Set ℕ := {c | ∃ L : ListAssignment V, IsNListAssignment L n ∧ G.col L = c}

/-- **The list color function** `P_ℓ(G, n)`: the least number of colorings achievable by any
`n`-list assignment. -/
noncomputable def listColorFunction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) : ℕ := sInf (G.colCounts n)

/-- **`P_ℓ(G, n) = P(G, n)` with a genuine polynomial on the right.** -/
theorem ecc_iff_listColorFunction_eq_eval {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (n : ℕ) :
    G.ECCAt n ↔ (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) := sorry

end SimpleGraph

namespace SimpleGraph.ERT

/-- Adjacency in a complete bipartite graph is decidable. -/
instance instDecidableRelCompleteBipartiteAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj := sorry

/-- `K_{n,nⁿ}`, the complete bipartite graph whose right side is indexed by the functions
`Fin n → Fin n`. -/
abbrev K (n : ℕ) : SimpleGraph (Fin n ⊕ (Fin n → Fin n)) :=
  completeBipartiteGraph (Fin n) (Fin n → Fin n)

/-- `K_{n,nⁿ}` is **not** `n`-choosable, witnessed by `L₀`. -/
theorem not_choosable (n : ℕ) : ¬ (K n).Choosable n := sorry

/-- `K_{n,nⁿ}` is `n`-colorable once `2 ≤ n`.  Together with `not_choosable` this is the
Erdős–Rubin–Taylor separation: `χ(K_{n,nⁿ}) ≤ n < χ_ℓ(K_{n,nⁿ})`. -/
theorem colorable (n : ℕ) (hn : 2 ≤ n) : (K n).Colorable n := sorry

end SimpleGraph.ERT

namespace SimpleGraph

/-! ### 4. Chordal graphs and Kostochka–Sidorenko

The first positive result. Adding a vertex joined to a *clique* preserves enumerative
chromatic-choosability at `n` (Kirov–Naimi's Lemma 1, `SimpleGraph.ECCAt.coneOn`), so any graph
built from nothing by repeated such attachments — a *simplicial elimination ordering*, read
backwards as a `cliqueTower` — is enumeratively chromatic-choosable at `n` for every `n`.

Dirac's theorem identifies those graphs as exactly the **chordal** ones, every cycle of length at
least `4` having a chord.  It is proved rather than assumed, so the Kostochka–Sidorenko theorem can
be claimed here in its own terms, with no tower data in the statement.  Dirac's lemma — a chordal
graph on a nonempty finite vertex type has a simplicial vertex, `exists_isSimplicialVertex` — is the
engine, and is in the library.
-/

/-- **The cone over `K`.** `coneOn G K` is the graph on `Option V` obtained from `G` by adding one
new vertex `none` joined to precisely the vertices in `K`. -/
def coneOn {V : Type*} (G : SimpleGraph V) (K : Finset V) : SimpleGraph (Option V) := sorry

/-- **A chordal graph.** Every cycle of length at least `4` has a chord: an edge of the graph
joining two vertices of the cycle which is not itself an edge of the cycle.  Phrased through
Mathlib's `SimpleGraph.Walk.IsChordless`. -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ {u : V} (c : G.Walk u u), c.IsCycle → 4 ≤ c.length → ¬ c.IsChordless

section

universe u

/-- The vertex type of `G` after `k` successive pendant attachments: `V` with `k` extra points. -/
def TowerV (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => Option (TowerV V k)

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

/-- **The simplicial condition.** `d.IsSimplicial` says that at every stage of the tower the set of
old vertices to which the new vertex is attached is a clique *of the graph existing at that
stage*. -/
def CliqueTowerData.IsSimplicial {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → CliqueTowerData V k → Prop
  | 0, _ => True
  | k + 1, d =>
      (cliqueTower G k d.1).IsClique ((d.2 : Finset (TowerV V k)) : Set (TowerV V k)) ∧
        CliqueTowerData.IsSimplicial G k d.1

/-- **The Kostochka–Sidorenko theorem, under its own name and unconditionally.** *Every chordal
graph is enumeratively chromatic-choosable at `n`, for every `n`.*

This is the statement the tower form `SimpleGraph.ecc_cliqueTower_of_isEmpty` could only
approximate, because "chordal" was undefined there.  The missing link is Dirac's lemma
(`SimpleGraph.exists_isSimplicialVertex`), now proved, so there is no hypothesis left to borrow. -/
theorem ecc_of_isChordal {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) : G.ECCAt n := sorry

/-- **Dirac's theorem.** *A finite graph is chordal if and only if it has a simplicial elimination
ordering*, presented backwards and constructively as a `SimpleGraph.cliqueTower` over the empty
graph. -/
theorem isChordal_iff_exists_cliqueTower {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsChordal ↔ ∃ (k : ℕ) (d : CliqueTowerData (Fin 0) k),
      CliqueTowerData.IsSimplicial (⊥ : SimpleGraph (Fin 0)) k d ∧
        Nonempty (G ≃g cliqueTower (⊥ : SimpleGraph (Fin 0)) k d) := sorry

end

/-! ### 5. Theorem 1: every cycle is enumeratively chromatic-choosable at `n`

The paper's main theorem.  A path is built by repeatedly attaching a pendant vertex; a cycle is a
path with its two ends joined, which is what `closePath` does.

The library has the count that drives the proof — `col(C, n) = n · A_{k-1}` for the mutually
recursive `A_k`, `B_k` of `ListColoring.pathA`/`pathB` (`colConst_closePath`), the two shapes of
`(n, n-1)`-list assignment on a path and their counts (`col_pathAssign`), the `n = 2` case by
rotation (`rotIso`, `ecc_closePath_two`), and the closed form
`(n-1)^v + (-1)^v (n-1)` for the cycle on `v` vertices (`colConst_closePath_chromatic`,
`listColorFunction_closePath_chromatic`).  Only the theorem itself is claimed.

The *same* attachment, iterated, is the **pendant tower**: the reading of a graph as its core with
degree-one vertices grown back on, which §7 and §8 are stated with.  `TowerData` and `pendantTower`
are declared here, next to `addPendant`, because that is all they are made of; Kirov–Naimi's
**Lemma 5** (`SimpleGraph.ecc_pendantTower_iff`) and its choosability analogue
(`SimpleGraph.choosable_pendantTower_iff`) are the two facts about them, and are in the library.
The vertex type they run over is §4's `TowerV`, shared with the cone towers: `Option` iterated `k`
times, whatever the new vertices are attached to.
-/

/-- `G` with one new pendant vertex `none`, attached to `v`. -/
def addPendant {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) := sorry

/-- `G` with one new vertex `none`, joined to both `u` and `v`. -/
def addPendantPair {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) := sorry

section

universe u

/-- The data specifying a tower of `k` pendant attachments: for each step, the already-existing
vertex at which the new pendant vertex is attached. -/
def TowerData (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => TowerData V k × TowerV V k

end

-- `pendantTower` is deliberately stated with `Type*`, and so is deliberately NOT inside the
-- `universe u` section above.  The comparator compares `ConstantVal`s, and a `ConstantVal`
-- carries `levelParams` as a list of *names*: alpha-equivalence is not enough, the universe
-- parameter has to end up with the same name here as in the library.  `ListColoring/Core.lean`
-- writes `TowerV` and `TowerData` as `(V : Type u)` against an explicit `universe u`, but
-- declares `pendantTower` against `variable {V : Type*}`, which auto-binds the universe as
-- `u_1`.  Reproducing that split is the only reason this one definition sits on its own.
-- (`ListAssignment` and `constList` above are pinned to `u_2` for the same reason.)

/-- **A tower of pendant attachments.** `pendantTower G k d` is the graph obtained from `G` by
attaching `k` pendant vertices one after another, the `i`-th of them at the vertex recorded in `d`
(which may itself be one of the earlier new vertices). -/
def pendantTower {V : Type*} (G : SimpleGraph V) :
    (k : ℕ) → TowerData V k → SimpleGraph (TowerV V k)
  | 0, _ => G
  | k + 1, d => (pendantTower G k d.1).addPendant d.2

end SimpleGraph

namespace ListColoring

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

/-- The path of length `k` closed up: `pathG k` together with one extra edge joining its two
terminal vertices.  For `k ≥ 2` this is the cycle on `k + 1` vertices. -/
def closePath : (k : ℕ) → SimpleGraph (PathV k)
  | 0 => ⊥
  | k + 1 => (pathG k).addPendantPair (pathEnd k) (pathStart k)

instance instDecidableRelClosePath : (k : ℕ) → DecidableRel (closePath k).Adj := sorry

/-- **Theorem 1 of Kirov–Naimi in full: every cycle is enumeratively chromatic-choosable at `n`,
for every `n ≥ 2`.** -/
theorem ecc_closePath_of_two_le {k m : ℕ} (hk : 2 ≤ k) :
    (closePath k).ECCAt (m + 2) := sorry

/-! ### 6. The machinery behind Theorem 1

Nothing is defined or claimed in this section; it is here so that the path still reads end to end.

Three technical steps carry Theorem 1, all in the library.  **Lemma 2**
(`SimpleGraph.exists_nested_of_bridge`): cutting a graph along a **bridge** and swapping colours on
one side does not increase the count, so the lists at the two ends of the bridge may be assumed
nested — the apparatus is `SimpleGraph.bridge`, `colAvoid`, `swapRight`, `col_bridge`,
`col_swapRight_add`.  **Lemma 4** (`ListColoring.col_lt_col_of_ssubset`): on a path, enlarging the
lists *strictly* increases the count.  **Lemma 3(b)(c)**
(`ListColoring.min_pathA_pathB_le_col`, `ListColoring.isPathShape_parity_of_minimizing`): every
`(n, n-1)`-assignment on a path admits at least `min(A_k, B_k)` colourings, and a *minimizing* one
has the shape dictated by the parity of `k` — with the predicates `ListColoring.IsNNAssign`,
`ListColoring.IsPathShape` and `SimpleGraph.Minimizing`, and the path splitting isomorphism
`ListColoring.pathSplitIso`.
-/

/-! ### 7. `2`-choosability: Rubin's theorem

Which graphs are `2`-choosable? Choosability is inherited by subgraphs
(`SimpleGraph.Choosable.mono`, `.comap`) and — the key reduction — is unchanged by attaching or
removing pendant vertices (`SimpleGraph.choosable_pendantTower_iff`), so a connected graph may be
replaced by its **core**: what is left after deleting degree-one vertices until none remain, or,
read backwards, the graph of which `G` is a `pendantTower`.  `CoreIs` spells that out, and the
alternatives `CoreIsVertex`, `CoreIsEvenCycle`, `CoreIsTheta` are the three cases Rubin's theorem
names.

Rubin's theorem says the `2`-choosable cores are exactly a single vertex, an even cycle, and the
theta graphs `θ_{2,2,2m}`.  **It is proved in this development**, and claimed here in full: both
directions, with the cases concrete rather than abstract propositions.  The `⟸` half is assembled
from Theorem 1 (`ListColoring.choosable_two_closePath_of_odd`) and
`ListColoring.choosable_theta`; the `⟹` half runs Rubin's own argument — pass to the core
(`ListColoring.hasCore`), which has minimum degree at least `2`, and extract from
`ListColoring.rubin_structure` either a spanning even cycle or a labelled `θ_{2,2,2m}`
(`ListColoring.exists_iso_closePath_of_two_regular`,
`ListColoring.exists_iso_theta_of_thetaData`).  The arity-general input to that argument is
`ListColoring.choosable_two_gtheta_iff`, in the library.

`instDecidableRelPathG` and `instDecidableRelTheta` are in the list for this section's sake alone:
`CoreIs G H` asks for a decidable `H`, and `pathG 0` and `theta m` are the `H`s that `CoreIsVertex`,
`CoreIsTheta` and §8's `CoreIsK23` name.
-/

/-- The vertex type of `θ_{2,2,2m}`. -/
abbrev ThetaV (m : ℕ) : Type := Option (Option (PathV (2 * m)))

/-- The theta graph `θ_{2,2,2m}`. -/
def theta (m : ℕ) : SimpleGraph (ThetaV m) :=
  coneOn (coneOn (pathG (2 * m)) {pathStart (2 * m), pathEnd (2 * m)})
    {some (pathStart (2 * m)), some (pathEnd (2 * m))}

instance instDecidableRelTheta : (m : ℕ) → DecidableRel (theta m).Adj := sorry

/-- **The core of `G` is `H`**: `G` is `H` with a finite tower of pendant vertices attached.

Kirov–Naimi's core is obtained from `G` by deleting vertices of degree one until none remain. Read
in reverse, that says `G` is built from its core by attaching pendant vertices one at a time, each
one at an arbitrary vertex of the graph built so far — which is `SimpleGraph.pendantTower`. The
statement is up to isomorphism because the tower lives on its own vertex type. -/
def CoreIs {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ∃ (k : ℕ) (d : TowerData W k), Nonempty (G ≃g pendantTower H k d)

/-- **The core of `G` is a single vertex.** `ListColoring.pathG 0` is the one-vertex graph — a
path of length zero. Equivalently, `G` is a tree. First alternative of Theorem 2, and of Rubin's
theorem. -/
def CoreIsVertex {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := CoreIs G (pathG 0)

/-- **The core of `G` is an even cycle**, i.e. a cycle on an even number of vertices. Since
`closePath k` has `k + 1` vertices, that is `Odd k`. Second alternative of Rubin's theorem. -/
def CoreIsEvenCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ k, Odd k ∧ 2 ≤ k ∧ CoreIs G (closePath k)

/-- **The core of `G` is `θ_{2,2,2m}` for some `m ≥ 1`.** Third alternative of Rubin's theorem. -/
def CoreIsTheta {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ m, 1 ≤ m ∧ CoreIs G (theta m)

/-- **Rubin's theorem.**

> A connected graph is `2`-choosable iff its core is a single vertex, an even cycle, or
> `θ_{2,2,2m}` for some `m ≥ 1`.

Due to **A. L. Rubin**, and published in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in
graphs*, Congr. Numer. **26** (1980), 125–157, pp. 131–134.  This `Prop` *is* the statement of
claim 8: the theorem below has it as its bare type. -/
def RubinTheorem : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (G.Choosable 2 ↔ (CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G))

/-- **Rubin's theorem, proved.**  Kirov–Naimi cite it; this development proves it, so nothing about
`2`-choosability is borrowed and Theorem 2 below needs no hypothesis.  Its statement is the body of
`RubinTheorem` above; there is no other place to read it. -/
theorem rubinTheorem : RubinTheorem := sorry

/-! ### 8. Enumerative chromatic-choosability at `2`: Theorem 2

The classification, and the end of the paper. `K₂,₃ = θ_{2,2,2}` is enumeratively
chromatic-choosable at `2` (Kirov–Naimi's Lemma 6, `SimpleGraph.ecc_K23`) while `θ_{2,2,2m}` is not
for `m ≥ 2` (`ListColoring.not_ecc_theta`); those two facts, plus §5's cycles and §4's chordal
graphs and the core reduction (Lemma 5, `SimpleGraph.ecc_pendantTower_iff`), turn §7's list of the
`2`-choosable graphs into a list of the enumeratively chromatic-choosable ones.

Where Rubin's theorem says "even cycle", Theorem 2 says "cycle": *every* cycle is enumeratively
chromatic-choosable at `2`, and the odd ones get there by not being `2`-colourable at all.  That is
the fourth alternative, `HasOddCycle`, and the bridge to it — a graph is `2`-colourable iff it
contains no odd cycle — is `ListColoring.hasOddCycle_of_not_colorable_two`, proved from scratch
here because Mathlib records the bipartite characterization as an open `TODO`.
-/

/-- **The core of `G` is a cycle.** `closePath k` is the cycle on `k + 1` vertices, and `2 ≤ k`
says it really is a cycle rather than a point or a single edge. No parity restriction: Theorem 2
says "is a cycle", not "is an even cycle". Second alternative of Theorem 2. -/
def CoreIsCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ k, 2 ≤ k ∧ CoreIs G (closePath k)

/-- **The core of `G` is `K₂,₃`.** `ListColoring.theta 1` is `θ_{2,2,2}`, which is `K₂,₃`; the
isomorphism is `ListColoring.k23IsoThetaOne`. Third alternative of Theorem 2. -/
def CoreIsK23 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := CoreIs G (theta 1)

/-- `G` **contains** a copy of `K`: an injection of the vertices of `K` into those of `G` carrying
edges to edges. Only a *subgraph* is asked for, not an induced one, which is all that a
choosability argument ever needs. -/
def Contains {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ a b, K.Adj a b → G.Adj (f a) (f b)

/-- **`G` contains an odd cycle**: a subgraph copy of a cycle on an odd number of vertices.

`closePath k` is the cycle on `k + 1` vertices, so `Even k` is what makes it odd. Fourth
alternative of Theorem 2. -/
def HasOddCycle {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop := ∃ k, Even k ∧ 2 ≤ k ∧ Contains G (closePath k)

/-- **Theorem 2 of Kirov–Naimi, with no hypothesis beyond connectivity.**

> A connected graph is 2-monophilic iff its core is a single vertex, is a cycle, is `K₂,₃`, or
> contains an odd cycle.

That is the paper's wording; "2-monophilic" is `SimpleGraph.ECCAt G 2`, *enumeratively
chromatic-choosable at `2`*.  Kirov–Naimi, Ars Combin. **124** (2016), 329–340
(arXiv:1004.5183), Theorem 2.  The one result they borrow — Rubin's theorem — is claim 8 above
rather than a hypothesis, so this is the theorem as they state it. -/
theorem ecc_two_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) :
    G.ECCAt 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G := sorry

end ListColoring

namespace SimpleGraph

/-! ### 9. Every graph, eventually

Donner's theorem: *every* graph is enumeratively chromatic-choosable at `n` once `n` is large
enough. The proof runs the Whitney expansion of §2 for an arbitrary list assignment rather than a
single palette (`SimpleGraph.listCount`, `col_eq_sum_powerset`), and yields more than the statement
claimed here — an explicit threshold, `SimpleGraph.ecc_of_two_pow_lt`: `n > 2^{|E(G)|}` suffices. -/

/-- **Donner's theorem (1992).** Every graph is enumeratively chromatic-choosable at `k` for all
sufficiently large `k`. -/
theorem exists_ecc_forall_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∃ N, ∀ k, N ≤ k → G.ECCAt k := sorry

end SimpleGraph
