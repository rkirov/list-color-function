import Mathlib
/-!
# List coloring and enumerative chromatic-choosability — the challenge statements

The statement surface of the `graph_coloring` development, a formalization of

> Radoslav Kirov and Ramin Naimi, *List coloring and `n`-monophilic graphs*,
> Ars Combinatoria (arXiv:1004.5183).

Everything is stated exactly as in the library; proofs and the decidability instances are
`sorry`, so "declaration uses `sorry`" is expected.  The comparator checks these statements
against `Submission.lean`, which imports the library; `config.json` lists what is claimed.
-/

open Finset

universe u

namespace SimpleGraph

/-! ### 1. Colouring a graph

`col(G, L)` counts the proper colourings that draw each vertex's colour from its own finite list
`L v`; `col(G, n)` is the special case where every list is the palette `{0, …, n-1}`.  Every claim
below is a statement about these two counts.
-/

/-- A **list assignment** for a graph on `V` gives each vertex a finite set of allowed colors. -/
abbrev ListAssignment (V : Type u) : Type u := V → Finset ℕ

/-- The constant list assignment sending every vertex to `{0, 1, …, n-1}`; the paper's `[n]`. -/
def constList (V : Type u) (n : ℕ) : ListAssignment V := fun _ => range n

/-- `f` is a proper coloring of `G`: adjacent vertices get distinct colors. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) (f : V → ℕ) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w

/-- Unlisted: only so that `colorings` can be written as a `Finset.filter`. -/
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

Defined by the Whitney subset expansion `∑_{S ⊆ E(G)} (-1)^{|S|} X^{c(S)}`, where `c(S)` counts
the connected components of the spanning subgraph with edge set `S`; the claim is that evaluating
it at `n` returns `col(G, n)`. -/

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

`G` is **`n`-choosable** if every `n`-list assignment admits a colouring, and **enumeratively
chromatic-choosable at `n`** if the constant assignment *minimizes* the number of colourings — the
paper's subject, claimed below to be exactly the condition `P_ℓ(G, n) = P(G, n)`.  Two
separations are claimed after it: the regime `χ(G) ≤ n < χ_ℓ(G)` is nonempty (Erdős–Rubin–Taylor),
and above `χ_ℓ` the property still fails for some graph at every `k ≥ 2` (the paper's §5).
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

namespace SimpleGraph.KN5

/-- **Kirov–Naimi, §5.**  For every `k ≥ 2` there is a graph that is `k`-choosable but not
enumeratively chromatic-choosable at `k`. -/
theorem exists_choosable_not_ecc_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ (V : Type) (iF : Fintype V) (iD : DecidableEq V) (G : SimpleGraph V)
      (iA : DecidableRel G.Adj), @Choosable V iF iD G iA k ∧ ¬ @ECCAt V iF iD G iA k := sorry

end SimpleGraph.KN5

namespace SimpleGraph

/-! ### 4. Chordal graphs and Kostochka–Sidorenko

Coning over a clique preserves enumerative chromatic-choosability (Kirov–Naimi's Lemma 1), and a
finite graph is built from nothing by such attachments exactly when it is **chordal** — Dirac's
theorem, proved in the library — which is what lets Kostochka–Sidorenko be claimed in its own
terms.
-/

/-- **A chordal graph.** Every cycle of length at least `4` has a chord: an edge of the graph
joining two vertices of the cycle which is not itself an edge of the cycle.  Phrased through
Mathlib's `SimpleGraph.Walk.IsChordless`. -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ {u : V} (c : G.Walk u u), c.IsCycle → 4 ≤ c.length → ¬ c.IsChordless

/-- **The Kostochka–Sidorenko theorem.** *Every chordal graph is enumeratively
chromatic-choosable at `n`, for every `n`.* -/
theorem ecc_of_isChordal {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) : G.ECCAt n := sorry

/-! ### 5. Theorem 1: every cycle is enumeratively chromatic-choosable at `n`

The paper's main theorem, claimed on Mathlib's `SimpleGraph.cycleGraph` so that the statement
involves no construction of this development.  The constructions below carry the rest of the
file: a cycle is a path — `pathG`, built by iterated `addPendant` — with its two ends joined
(`closePath`), and the same attachment iterated is the **pendant tower**, the reading of a graph
as its core with degree-one vertices grown back on, which §7 and §8 are stated with.
-/

/-- Adjacency for `G` with a new vertex `none` joined to `v` alone. -/
def addPendantAdj {V : Type*} (G : SimpleGraph V) (v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some b => b = v
  | some a, none => a = v
  | some a, some b => G.Adj a b

/-- `G` with one new pendant vertex `none`, attached to `v`. -/
def addPendant {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) where
  Adj := G.addPendantAdj v
  symm := ⟨by rintro (_ | a) (_ | b) h <;> simp_all [addPendantAdj, G.adj_comm]⟩
  loopless := ⟨by rintro (_ | a) h <;> simp_all [addPendantAdj]⟩

/-- Adjacency for `G` with a new vertex `none` joined to both `u` and `v` (and nothing else). -/
def addPendantPairAdj {V : Type*} (G : SimpleGraph V) (u v : V) : Option V → Option V → Prop
  | none, none => False
  | none, some b => b = u ∨ b = v
  | some a, none => a = u ∨ a = v
  | some a, some b => G.Adj a b

/-- `G` with one new vertex `none`, joined to both `u` and `v`. -/
def addPendantPair {V : Type*} (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) where
  Adj := G.addPendantPairAdj u v
  symm := ⟨by rintro (_ | a) (_ | b) h <;> simp_all [addPendantPairAdj, G.adj_comm]⟩
  loopless := ⟨by rintro (_ | a) h <;> simp_all [addPendantPairAdj]⟩

/-- The vertex type of `G` after `k` successive pendant attachments: `V` with `k` extra points. -/
def TowerV (V : Type u) : ℕ → Type u
  | 0 => V
  | k + 1 => Option (TowerV V k)

/-- The data specifying a tower of `k` pendant attachments: for each step, the already-existing
vertex at which the new pendant vertex is attached. -/
def TowerData (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => TowerData V k × TowerV V k

/-- **A tower of pendant attachments.** `pendantTower G k d` is the graph obtained from `G` by
attaching `k` pendant vertices one after another, the `i`-th of them at the vertex recorded in `d`
(which may itself be one of the earlier new vertices). -/
def pendantTower {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → TowerData V k → SimpleGraph (TowerV V k)
  | 0, _ => G
  | k + 1, d => (pendantTower G k d.1).addPendant d.2

/-- **Theorem 1 of Kirov–Naimi: every cycle is enumeratively chromatic-choosable at `n`, for
every `n ≥ 2`.**  `cycleGraph n` is Mathlib's cycle graph on `n` vertices. -/
theorem ecc_cycleGraph_of_three_le {n m : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).ECCAt (m + 2) := sorry

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

/-! ### 6. The machinery behind Theorem 1

Nothing is defined or claimed here.  Theorem 1 rests on three steps, all in the library: Lemma 2,
swapping across a bridge makes the end lists nested; Lemma 4, enlarging lists on a path strictly
increases the count; Lemma 3(b)(c), the `min(A_k, B_k)` lower bound and the parity shape of a
minimizing assignment.
-/

/-! ### 7. `2`-choosability: Rubin's theorem

Choosability is unchanged by attaching or removing pendant vertices, so a connected graph may be
replaced by its **core**: the graph of which it is a `pendantTower`.  `CoreIs` spells that out,
and `CoreIsVertex`, `CoreIsEvenCycle`, `CoreIsTheta` are the three cases Rubin's theorem names.
It is proved in this development and claimed in full, both directions.

`instDecidableRelPathG` and `instDecidableRelTheta` are listed for this section's sake alone:
`CoreIs G H` asks for a decidable `H`.
-/

end ListColoring

namespace SimpleGraph

/-- Adjacency for the cone: `none` is joined to exactly the vertices of `K`. -/
def coneAdj {V : Type*} (G : SimpleGraph V) (K : Finset V) : Option V → Option V → Prop
  | some a, some b => G.Adj a b
  | none, some b => b ∈ K
  | some a, none => a ∈ K
  | none, none => False

/-- **The cone over `K`.** `coneOn G K` is the graph on `Option V` obtained from `G` by adding one
new vertex `none` joined to precisely the vertices in `K`. -/
def coneOn {V : Type*} (G : SimpleGraph V) (K : Finset V) : SimpleGraph (Option V) where
  Adj := coneAdj G K
  symm := ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact h.ne rfl⟩

end SimpleGraph

namespace ListColoring

open SimpleGraph

/-- The vertex type of `θ_{2,2,2m}`. -/
abbrev ThetaV (m : ℕ) : Type := Option (Option (PathV (2 * m)))

/-- The theta graph `θ_{2,2,2m}`. -/
def theta (m : ℕ) : SimpleGraph (ThetaV m) :=
  coneOn (coneOn (pathG (2 * m)) {pathStart (2 * m), pathEnd (2 * m)})
    {some (pathStart (2 * m)), some (pathEnd (2 * m))}

instance instDecidableRelTheta : (m : ℕ) → DecidableRel (theta m).Adj := sorry

/-- **The core of `G` is `H`**: `G` is `H` with a finite tower of pendant vertices attached — the
reverse reading of "delete degree-one vertices until none remain".  Up to isomorphism, because the
tower lives on its own vertex type. -/
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

A. L. Rubin, in Erdős–Rubin–Taylor, *Choosability in graphs*, Congr. Numer. **26** (1980),
125–157.  This `Prop` *is* the claimed statement: the theorem below has it as its bare type. -/
def RubinTheorem : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (G.Choosable 2 ↔ (CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G))

/-- **Rubin's theorem.**  The paper cites it; this development proves it.  Its statement is the
body of `RubinTheorem` above; there is no other place to read it. -/
theorem rubinTheorem : RubinTheorem := sorry

/-! ### 8. Enumerative chromatic-choosability at `2`: Theorem 2

`K₂,₃ = θ_{2,2,2}` is enumeratively chromatic-choosable at `2` (Kirov–Naimi's Lemma 6) and
`θ_{2,2,2m}` with `m ≥ 2` is not; with §5's cycles, §4's chordal graphs and the core reduction
(Lemma 5), that turns §7's list into Theorem 2's.  Where Rubin says "even cycle", Theorem 2 says
"cycle": odd cycles qualify by not being `2`-colourable at all, which is the fourth alternative,
`HasOddCycle`.
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

The paper's wording; "2-monophilic" is `SimpleGraph.ECCAt G 2`.  Kirov–Naimi, Ars Combin. **124**
(2016), 329–340, Theorem 2.  Rubin's theorem, which the paper quotes, is claimed above. -/
theorem ecc_two_iff {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) :
    G.ECCAt 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G := sorry

end ListColoring

namespace SimpleGraph

/-! ### 9. Every graph, eventually

Donner's theorem.  The library proves more than is claimed: the explicit threshold
`n > 2^{|E(G)|}` suffices (`SimpleGraph.ecc_of_two_pow_lt`). -/

/-- **Donner's theorem (1992).** Every graph is enumeratively chromatic-choosable at `k` for all
sufficiently large `k`. -/
theorem exists_ecc_forall_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∃ N, ∀ k, N ≤ k → G.ECCAt k := sorry

end SimpleGraph
