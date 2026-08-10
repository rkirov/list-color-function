import Mathlib
/-!
# List coloring and `n`-monophilic graphs — the challenge statements

This file is the *statement surface* of the `graph_coloring` development, a formalization of

> Radoslav Kirov and Ramin Naimi, *List coloring and `n`-monophilic graphs*,
> Ars Combinatoria (arXiv:1004.5183),

together with the chromatic-polynomial / list-color-function reformulation, Dirac's theorem and
Donner's theorem.  Every declaration below is stated exactly as in the library; the theorems are
left with a placeholder proof, so that the comparator can check a submission's statements against
these.  Compiling this file is *expected* to report "declaration uses `sorry`" — that is the point.

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
8. `choosable_two_of_rubinFamily` — **Rubin**, the direction that is proved
9. `ecc_two_iff_of_rubin_hard` — **Kirov–Naimi, Theorem 2**
10. `exists_ecc_forall_ge` — **Donner**: every graph is enumeratively chromatic-choosable at `n` for
    large `n`

`ERT.colorable` is the tenth; on its own `not_choosable` says only that `χ_ℓ > n`, and the point of
the example is the *separation*.

## What is defined

`definition_names` is exactly what those ten statements need, computed rather than curated: the 18
definitions reachable from their types, plus the 16 notions those 18 are written in terms of, so
that the file can be read without the library.  No definition is here for any other reason; in
particular only four are `Fintype`/`DecidableEq`/`DecidableRel` instances, and each of the four
occurs in the *type* of a listed theorem — `(closePath k).ECCAt (m + 2)` does not typecheck
without them.

Most definitions carry their **real bodies**, so the file reads as a specification; the comparator
never inspects the body of a `definition_names` entry.  Placeholders remain only where the body is
not a statement: the graph constructions built as `SimpleGraph` structure instances with
tactic-proved `symm`/`loopless` fields (`coneOn`, `addPendant`, `addPendantPair`), and the four
decidability instances.  Two bodies are forced rather than chosen — `ListAssignment`, whose values
are applied as functions in other statements, and `ThetaV`, whose instances are found by unfolding
the abbreviation.  Two declarations appear without being listed, because a *body* rather than a
statement needs them: `instDecidableIsProperColoring` (so `colorings` can be a `Finset.filter`) and
`decidableRelFromEdgeSetCoe` (so `compCount` can count components).

## How to read it

The nine sections follow the path the book's Part I takes.  Sections that no longer carry a claim
still carry the story: §1 introduces the vocabulary the rest is written in, and §6 is prose only,
pointing at the machinery in the library.  Everything the library proves and this file does not
claim — Kirov–Naimi's Lemmas 1–6, the three regimes, the explicit threshold `n > 2^{|E|}`, Rubin's
`⟸` for each family separately, Dirac's lemma, the chromatic polynomial of a cycle in closed form —
is still there, under the names given in the section headers below.

Two places where Lean fought the teaching order.  `ListAssignment` and `constList` are declared in
§1 although they belong to §3, because `col` is defined on a list assignment and the palette count
`colConst` is its special case.  And the chromatic polynomial sits at §2, before lists, which pulls
`compCount` and the `fromEdgeSet` decidability instance forward with it.
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
-/

/-- `G` with one new pendant vertex `none`, attached to `v`. -/
def addPendant {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) := sorry

/-- `G` with one new vertex `none`, joined to both `u` and `v`. -/
def addPendantPair {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) := sorry

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

/-! ### 7. `2`-choosability: Rubin's list

Which graphs are `2`-choosable? Choosability is inherited by subgraphs
(`SimpleGraph.Choosable.mono`, `.comap`) and — the key reduction — is unchanged by attaching or
removing pendant vertices (`SimpleGraph.choosable_pendantTower_iff`, with the `pendantTower`
construction), so a connected graph may be replaced by its **core**. Rubin's theorem says the
`2`-choosable cores are exactly a single vertex, an even cycle, and the theta graphs `θ_{2,2,2m}`;
`RubinFamily` is that list.

The `⟸` direction is claimed here.  Its three cases are in the library: the even-cycle case is a
corollary of Theorem 1 (`ListColoring.choosable_two_closePath_of_odd`) and the theta case is
`ListColoring.choosable_theta`.  The `⟹` direction is the one piece of the story no proof assistant
has, and §8 borrows it explicitly.
-/

/-- The vertex type of `θ_{2,2,2m}`. -/
abbrev ThetaV (m : ℕ) : Type := Option (Option (PathV (2 * m)))

/-- The theta graph `θ_{2,2,2m}`. -/
def theta (m : ℕ) : SimpleGraph (ThetaV m) :=
  coneOn (coneOn (pathG (2 * m)) {pathStart (2 * m), pathEnd (2 * m)})
    {some (pathStart (2 * m)), some (pathEnd (2 * m))}

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

end ListColoring

namespace SimpleGraph

/-! ### 8. Enumerative chromatic-choosability at `2`: Theorem 2

The classification. `K₂,₃ = θ_{2,2,2}` is enumeratively chromatic-choosable at `2` (Kirov–Naimi's
Lemma 6, `SimpleGraph.ecc_K23`) while `θ_{2,2,2m}` is not for `m ≥ 2`
(`ListColoring.not_ecc_theta`); those two facts, plus §5's cycles and §4's chordal graphs and the
core reduction (Lemma 5, `SimpleGraph.ecc_pendantTower_iff`), turn Rubin's list into a list of the
graphs that are enumeratively chromatic-choosable at `2`.

Rubin's `⟹` direction enters as an explicit hypothesis, with the three alternatives kept abstract
so that exactly what is borrowed is visible in the signature and nothing about cores can be
smuggled in.
-/

/-- **Theorem 2 of Kirov–Naimi, borrowing only the hard direction of Rubin's theorem.** -/
theorem ecc_two_iff_of_rubin_hard {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {CoreIsVertex CoreIsEvenCycle : Prop} {CoreIsTheta : ℕ → Prop}
    (rubin : G.Choosable 2 →
      CoreIsVertex ∨ CoreIsEvenCycle ∨ ∃ m, 1 ≤ m ∧ CoreIsTheta m)
    (hvertex : CoreIsVertex → G.ECCAt 2)
    (hcycle : CoreIsEvenCycle → G.ECCAt 2)
    (hK23 : CoreIsTheta 1 → G.ECCAt 2)
    (htheta : ∀ m, 2 ≤ m → CoreIsTheta m → ¬ G.ECCAt 2) :
    G.ECCAt 2 ↔ ¬ G.Colorable 2 ∨ CoreIsVertex ∨ CoreIsEvenCycle ∨ CoreIsTheta 1 := sorry

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
