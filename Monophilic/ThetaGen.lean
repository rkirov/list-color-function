/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.ThetaClass
import Monophilic.NotChoosable

/-!
# Generalized theta graphs of arbitrary arity

A **generalized theta graph** `Θ(k₁, …, k_n)` is two distinguished *branch* vertices joined by `n`
internally disjoint paths — *arms* — of edge-lengths `k₁, …, k_n`. It is a simple graph exactly
when every `kᵢ ≥ 1` and at most one `kᵢ = 1` (two arms of length one would be a double edge).
`Monophilic.RubinHard` builds the three-arm case `Monophilic.thetaGen a b c`; this file builds
`Monophilic.gtheta ks` for a list `ks` of arm lengths of any length, and classifies which of them
are `2`-choosable:

> For `n ≥ 3`, `Θ(k₁, …, k_n)` is `2`-choosable **iff** `n = 3` and the multiset of lengths is
> `{2, 2, 2m}` for some `m ≥ 1`.

## Attribution

The classification proved here is **not new**. It is a component of **Rubin's theorem** (A. L.
Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West Coast Conf. on
Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congressus Numerantium
**26**, Utilitas Math., Winnipeg, **1980**, pp. 125–157; Zbl 0469.05032, no DOI — `1979` is the
conference year and `1980` the year of the proceedings volume, see the verification notes of
`references.md`), which says that a connected graph is `2`-choosable exactly when its core is
`K₁`, an even cycle, or `θ_{2,2,2m}`. As a *statement*, the arity-`n` classification below is a
corollary of Rubin's theorem: a generalized theta of minimum degree `≥ 2` is its own core, so
Rubin's list decides it. We nevertheless prove it **directly from list assignments**, so that it
can be fed into the proof of Rubin's theorem without circularity — `Monophilic.RubinHard` consumes
the three-arm case as `Monophilic.ThetaClassification`. Nothing here may therefore appeal to
Rubin's theorem, and nothing does.

The other half of Rubin's hard direction is a structural statement about connected graphs of
minimum degree `≥ 2` that are not cycles, and **no correct form of it is formalized here**. Two
candidate forms have already been refuted in this repository, both of them its own inventions and
neither the literature's; `Monophilic.Rubin` and the section "A removed definition, and why it must
stay removed" in `Monophilic.RubinHard` record the refutations, and `plan.md` records what a
correct statement would need. Neither should be reintroduced.

The first refutation is the reason this file exists. Reading "theta" as the *three-path* graph
makes the claim false, and the counterexample is exactly the graph the arity-four case below
settles: `K₂,₄ = Θ(2, 2, 2, 2)` is connected, has minimum degree `2`, is not a cycle, is bipartite,
and the only three-arm theta inside it is the *good* `θ_{2,2,2}` — yet it is not `2`-choosable
(`Monophilic.not_choosable_two_K24`). Three-arm thetas alone therefore do not suffice, which is
what the arity-`≥ 4` half of this file supplies. The natural repair — replacing three-arm thetas by
generalized ones, together with two cycles meeting in at most one vertex — is *also* false, as
`K₃,₃` minus an edge shows. So the classification proved here is necessary for the structural step
and nowhere near sufficient.

No part of this file is claimed as new mathematics. Everything that is not Rubin's is
mechanization scaffolding: the inductions along an arm of unbounded length, and the bookkeeping
that reads a coloring of `Fin (Σ(kᵢ - 1) + 2)` as a function of vertex indices.

For contrast — because the graphs look the same — Chi, Lee, Morrissette, Mudrock, Nguyen and
Whatley (arXiv:2605.10861, 2026), Theorem 4, prove a *different* statement about three-arm thetas:
`Θ(l₁, l₂, l₃)` with `l₂, l₃ ≥ 2` fails to be *enumeratively chromatic-choosable*
(`P_ℓ(G, m) = P(G, m)` for every `m`, a counting property) exactly when the three lengths share a
parity and are not all `2`. That is a statement about counting list colorings of three-arm thetas,
proved by DP-coloring; the present file is about the *existence* of a list coloring, for arbitrary
arity.

## The construction

`gtheta ks` is laid out on `Fin (gsize ks + 2)`, where `gsize ks = Σ (kᵢ - 1)` is the total number
of *interior* vertices. Writing `mᵢ = kᵢ - 1`, the indices

* `0, …, m₁ - 1` are the interior of the first arm, in order from the first branch vertex;
* `m₁, …, m₁ + m₂ - 1` the interior of the second, and so on;
* `gsize ks` and `gsize ks + 1` are the two branch vertices.

An arm with `kᵢ = 1` has no interior vertex and contributes the single edge joining the two branch
vertices. The layout matches `Monophilic.thetaGen` exactly when `ks = [a, b, c]`, which is why
`Monophilic.gAdjB_triple` is an equality of Booleans rather than an isomorphism.

## The argument

Give the two branch vertices two-element lists `LS` and `LT`. A coloring then consists of a pair
`(α, β) ∈ LS × LT` of branch colors together with a coloring of the interior of each arm, and an
arm **blocks** `(α, β)` when its lists leave no interior coloring compatible with `α` and `β`
(`Monophilic.ArmBlocks`). If every one of the four pairs is blocked by some arm, there is no
coloring at all (`Monophilic.gcol_gBadLists_eq_zero`). Two gadgets suffice:

* an arm of length `1` — no interior at all — blocks exactly the pairs with `α = β`;
* an arm of length `≥ 2` blocks any single prescribed pair `(α, β)` with `α ≠ β`, through the
  forced chain `Monophilic.gArmLists`.

With four arms of length `≥ 2` one takes `LS = {1, 2}`, `LT = {3, 4}` and blocks the four pairs
one apiece. With one arm of length `1` and three of length `≥ 2` one takes `LS = {1, 2}`,
`LT = {2, 3}`: the short arm kills `(2, 2)` and the other three kill the rest. Since at most one
arm has length `1`, every valid shape with `n ≥ 4` falls into one case or the other — arity `≥ 4`
needs *less* than arity `3`, where the three arms must be juggled by parity.

## Main definitions

* `Monophilic.gtheta` : the generalized theta graph `Θ(k₁, …, k_n)`
* `Monophilic.ArmBlocks` : an arm's lists block a pair of branch colors
* `Monophilic.gArmLists`, `Monophilic.roleA`, `Monophilic.roleB`, `Monophilic.gBadLists` : the
  witness list assignments
* `Monophilic.ValidArms`, `Monophilic.GoodArms` : normalized shapes, and Rubin's shape

## Main results

* `Monophilic.gAdjB_triple`, `Monophilic.choosable_gtheta_triple_iff` : **three arms agree with
  `Monophilic.thetaGen`**, so the three-arm classification transfers instead of being redone
* `Monophilic.gArmBlocks` : **the forced chain along a blocking arm**, for any arity
* `Monophilic.gcol_gBadLists_eq_zero` : **blocking every branch pair leaves no coloring**
* `Monophilic.not_choosable_two_gtheta_of_four` : **no generalized theta with `n ≥ 4` arms is
  `2`-choosable**
* `Monophilic.choosable_two_gtheta_iff` : **the classification**, for every `n ≥ 3`
* `Monophilic.not_choosable_two_K24` : `K_{2,4}` is not `2`-choosable, via the arity-`4` case
-/

open Finset

namespace Monophilic

open SimpleGraph

set_option maxRecDepth 100000

/-! ### The generalized theta graph -/

/-- The total number of **interior** vertices of `Θ(k₁, …, k_n)`: arm `i` contributes `kᵢ - 1` of
them, and the two branch vertices are counted separately. -/
def gsize (ks : List ℕ) : ℕ := (ks.map (fun k => k - 1)).sum

/-- A theta with no arms has no interior vertices. -/
@[simp] theorem gsize_nil : gsize [] = 0 := rfl

/-- Adding an arm of length `k` adds `k - 1` interior vertices. -/
@[simp] theorem gsize_cons (k : ℕ) (ks : List ℕ) : gsize (k :: ks) = (k - 1) + gsize ks := rfl

/-- Adjacency of `Θ(k₁, …, k_n)`, read on indices and before symmetrizing: the union over the arms
of `Monophilic.armStepB`, whose interiors start at the running offsets `0`, `k₁ - 1`,
`(k₁ - 1) + (k₂ - 1)`, … . -/
def gAdjAux : List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], _, _, _, _, _ => false
  | k :: ks, o, ps, pt, x, y =>
      armStepB o (k - 1) ps pt x y || gAdjAux ks (o + (k - 1)) ps pt x y

/-- Adjacency of `Θ(k₁, …, k_n)` on indices: the two branch vertices are the two largest indices
`gsize ks` and `gsize ks + 1`. -/
def gAdjB (ks : List ℕ) (x y : ℕ) : Bool := gAdjAux ks 0 (gsize ks) (gsize ks + 1) x y

/-- The vertex type of `Θ(k₁, …, k_n)`: `Σ(kᵢ - 1)` interior vertices and two branch vertices. -/
abbrev GTV (ks : List ℕ) : Type := Fin (gsize ks + 2)

/-- **The generalized theta graph `Θ(k₁, …, k_n)`**: two branch vertices joined by `n` internally
disjoint paths, of edge-lengths `k₁, …, k_n`. Compare `Monophilic.thetaGen a b c`, which is the
three-arm case on the very same layout (`Monophilic.gAdjB_triple`). -/
def gtheta (ks : List ℕ) : SimpleGraph (GTV ks) where
  Adj x y := x ≠ y ∧ (gAdjB ks x.val y.val ∨ gAdjB ks y.val x.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in `Monophilic.gtheta` is decidable, since it is read off a Boolean. -/
instance instDecidableRelGtheta (ks : List ℕ) : DecidableRel (gtheta ks).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧
    (gAdjB ks x.val y.val = true ∨ gAdjB ks y.val x.val = true)))

/-! `Θ(k₁, …, k_n)` has `Σkᵢ - n + 2` vertices and `Σkᵢ` edges; the two branch vertices have degree
`n` and every other vertex has degree `2`. -/

/-- `Θ(k₁, …, k_n)` really is a generalized theta graph: `Σkᵢ` edges, and every vertex has degree
`2` except the two branch vertices — the two largest indices — which have degree `n`. -/
def gthetaShapeOk (ks : List ℕ) : Bool :=
  decide ((gtheta ks).edgeFinset.card = ks.sum ∧
    ∀ v : GTV ks, (gtheta ks).degree v = if v.val < gsize ks then 2 else ks.length)

#guard Fintype.card (GTV [2, 2, 2, 2]) = 6
#guard (gtheta [2, 2, 2, 2]).edgeFinset.card = 8
#guard Fintype.card (GTV [1, 2, 2, 2]) = 5
#guard (gtheta [1, 2, 2, 2]).edgeFinset.card = 7
#guard Fintype.card (GTV [3, 4, 5]) = 11
#guard (gtheta [3, 4, 5]).edgeFinset.card = 12
#guard ((univ : Finset (GTV [2, 2, 2, 2])).image fun v => (gtheta [2, 2, 2, 2]).degree v)
  = {2, 4}
#guard ((univ : Finset (GTV [1, 3, 3, 4])).image fun v => (gtheta [1, 3, 3, 4]).degree v)
  = {2, 4}
#guard ((univ : Finset (GTV [2, 2, 2, 2, 2])).filter
  fun v => (gtheta [2, 2, 2, 2, 2]).degree v = 5).card = 2

#guard [[1, 2, 2], [2, 2, 2], [2, 3, 4], [3, 3, 3], [1, 2, 2, 2], [2, 2, 2, 2], [2, 2, 3, 3],
  [1, 3, 3, 4], [2, 2, 2, 2, 2], [1, 2, 2, 3, 3], [2, 3, 4, 5, 6]].all gthetaShapeOk

/-! ### Where an arm sits

Pure bookkeeping: the interior of arm `i` occupies the `kᵢ - 1` indices starting at
`gsize (ks.take i)`. Nothing below is mathematics; it is the price of laying the graph out on
`Fin (gsize ks + 2)` instead of on a dependent sum over the arms. -/

/-- The offset of arm `i` grows by that arm's interior size. -/
theorem gsize_take_succ (ks : List ℕ) (i : ℕ) (hi : i < ks.length) :
    gsize (ks.take (i + 1)) = gsize (ks.take i) + (ks[i] - 1) := by
  induction ks generalizing i with
  | nil => simp at hi
  | cons k ks ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < ks.length := by simpa using hi
          simp only [List.take_succ_cons, gsize_cons, ih i hi', List.getElem_cons_succ]
          omega

/-- Every arm's interior fits inside the interior of the whole graph. -/
theorem gsize_take_le (ks : List ℕ) (i : ℕ) : gsize (ks.take i) ≤ gsize ks := by
  induction ks generalizing i with
  | nil => simp
  | cons k ks ih =>
      cases i with
      | zero => simp
      | succ i => simpa using ih i

/-- The interior of arm `i` lies below `gsize ks`, so it misses the two branch vertices. -/
theorem gsize_take_add_le (ks : List ℕ) (i : ℕ) (hi : i < ks.length) :
    gsize (ks.take i) + (ks[i] - 1) ≤ gsize ks := by
  rw [← gsize_take_succ ks i hi]
  exact gsize_take_le ks (i + 1)

/-- A step along arm `i` is a step of the whole graph. -/
theorem gAdjAux_of_armStepB (ks : List ℕ) (i : ℕ) (hi : i < ks.length) (o ps pt x y : ℕ)
    (h : armStepB (o + gsize (ks.take i)) (ks[i] - 1) ps pt x y = true) :
    gAdjAux ks o ps pt x y = true := by
  induction ks generalizing i o with
  | nil => simp at hi
  | cons k ks ih =>
      cases i with
      | zero =>
          simp only [List.take_zero, gsize_nil, Nat.add_zero, List.getElem_cons_zero] at h
          simp only [gAdjAux, Bool.or_eq_true]
          exact Or.inl h
      | succ i =>
          have hi' : i < ks.length := by simpa using hi
          simp only [List.take_succ_cons, gsize_cons, List.getElem_cons_succ] at h
          simp only [gAdjAux, Bool.or_eq_true]
          refine Or.inr (ih i hi' (o + (k - 1)) ?_)
          rwa [show o + (k - 1) + gsize (ks.take i) = o + ((k - 1) + gsize (ks.take i)) from
            by omega]

/-- A step of arm `i` of `Θ(k₁, …, k_n)`, in the graph's own adjacency. -/
theorem gAdjB_of_armStepB (ks : List ℕ) (i : ℕ) (hi : i < ks.length) (x y : ℕ)
    (h : armStepB (gsize (ks.take i)) (ks[i] - 1) (gsize ks) (gsize ks + 1) x y = true) :
    gAdjB ks x y = true :=
  gAdjAux_of_armStepB ks i hi 0 _ _ x y (by simpa using h)

/-! The four steps an arm contributes. These repeat, for the general model, the private
`armStepB` lemmas of `Monophilic.ThetaClass`. -/

/-- The first interior vertex of an arm is joined to the first branch vertex. -/
private theorem armStep_head (o m ps pt : ℕ) (hm : m ≠ 0) : armStepB o m ps pt ps o = true := by
  simp only [armStepB, if_neg hm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  exact Or.inl (Or.inl ⟨trivial, trivial⟩)

/-- Consecutive interior vertices of an arm are joined. -/
private theorem armStep_mid (o m ps pt j : ℕ) (hj : j + 1 < m) :
    armStepB o m ps pt (o + j) (o + j + 1) = true := by
  simp only [armStepB, if_neg (show ¬ (m = 0) from by omega), Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, and_true]
  omega

/-- The last interior vertex of an arm is joined to the second branch vertex. -/
private theorem armStep_last (o m ps pt : ℕ) (hm : m ≠ 0) :
    armStepB o m ps pt (o + (m - 1)) pt = true := by
  simp only [armStepB, if_neg hm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, and_true]
  omega

/-- An arm of length one is the single edge joining the two branch vertices. -/
private theorem armStep_direct (o ps pt : ℕ) : armStepB o 0 ps pt ps pt = true := by
  simp [armStepB]

/-! ### Three arms: agreement with `Monophilic.thetaGen`

`Monophilic.thetaGen a b c` uses the very same layout, so the two adjacency Booleans are equal on
the nose once the arithmetic `gsize [a, b, c] = a + b + c - 3` is discharged. Choosability then
transfers both ways along the identity on indices, and the three-arm classification of
`Monophilic.ThetaClass` is inherited rather than reproved. -/

/-- The vertex counts agree. -/
theorem gsize_triple {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    gsize [a, b, c] + 2 = a + b + c - 1 := by
  simp only [gsize_cons, gsize_nil]
  omega

/-- **The adjacencies agree**: `Θ(a, b, c)` in the general model *is* `Monophilic.thetaGen a b c`,
index for index. -/
theorem gAdjB_triple {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (x y : ℕ) :
    gAdjB [a, b, c] x y = thetaGenAdjB a b c x y := by
  have h1 : gsize [a, b, c] = a + b + c - 3 := by simp only [gsize_cons, gsize_nil]; omega
  have h2 : (0 : ℕ) + (a - 1) = a - 1 := by omega
  have h3 : a - 1 + (b - 1) = a + b - 2 := by omega
  have h4 : a + b + c - 3 + 1 = a + b + c - 2 := by omega
  simp only [gAdjB, gAdjAux, h1, h2, h3, h4, thetaGenAdjB, Bool.or_false, Bool.or_assoc]

/-- **Choosability transfers between the two three-arm models**, in both directions. -/
theorem choosable_gtheta_triple_iff {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (n : ℕ) :
    (gtheta [a, b, c]).Choosable n ↔ (thetaGen a b c).Choosable n := by
  have hcard : gsize [a, b, c] + 2 = a + b + c - 1 := gsize_triple ha hb hc
  constructor
  · refine fun h => Choosable.comap h (f := Fin.cast hcard.symm) (Fin.cast_injective _) ?_
    rintro u v ⟨hne, huv⟩
    refine ⟨fun hc' => hne (Fin.val_injective (by simpa using congrArg Fin.val hc')), ?_⟩
    simpa only [Fin.val_cast, gAdjB_triple ha hb hc] using huv
  · refine fun h => Choosable.comap h (f := Fin.cast hcard) (Fin.cast_injective _) ?_
    rintro u v ⟨hne, huv⟩
    refine ⟨fun hc' => hne (Fin.val_injective (by simpa using congrArg Fin.val hc')), ?_⟩
    simpa only [Fin.val_cast, ← gAdjB_triple ha hb hc] using huv

/-! ### What an arm blocks

Fix two-element lists `LS`, `LT` at the two branch vertices. A coloring of `Θ(k₁, …, k_n)` from a
list assignment consists of a pair `(α, β) ∈ LS × LT` together with a coloring of each arm's
interior, and an arm **blocks** `(α, β)` when its own lists rule that pair out. -/

/-- **An arm blocks a pair of branch colors.** `m` is the number of interior vertices of the arm
and `L` their lists, read from the branch vertex carrying `α`; the five hypotheses are exactly what
a coloring of the ambient graph hands over — membership in the lists, properness along the arm,
properness at the two ends, and, when the arm is a single edge, properness across it. -/
def ArmBlocks (m : ℕ) (L : ℕ → Finset ℕ) (α β : ℕ) : Prop :=
  ∀ g : ℕ → ℕ, (∀ j, j < m → g j ∈ L j) → (∀ j, j + 1 < m → g j ≠ g (j + 1)) →
    (1 ≤ m → g 0 ≠ α) → (1 ≤ m → g (m - 1) ≠ β) → (m = 0 → α ≠ β) → False

/-- **An arm of length one blocks exactly the pairs with equal branch colors.** It is the single
edge joining the two branch vertices, so it forbids `α = β` and nothing else. -/
theorem armBlocks_direct (L : ℕ → Finset ℕ) (α : ℕ) : ArmBlocks 0 L α α :=
  fun _ _ _ _ _ hd => hd rfl rfl

/-- The lists along an arm with `m` interior vertices which blocks the single pair `(α, β)` of
branch colors, `j` being the position along the arm counted from the branch vertex carrying `α`.
For `m = 1` the lone interior vertex simply gets `{α, β}`. For `m ≥ 2` the chain of forced colors
is `5, β, 5, …` when `m` is even and `5, 6, β, 5, β, …` when `m` is odd, the detour through the
auxiliary color `6` correcting the parity; the list at position `j` is the pair of forced colors at
`j - 1` and `j`. Compare `Monophilic.armBlockLists`, which does the same job for three arms with
`3` and `4` as its auxiliary colors — here `1, 2, 3, 4` are all needed for the branch vertices. -/
def gArmLists (α β m j : ℕ) : Finset ℕ :=
  if m = 1 then {α, β}
  else if m % 2 = 0 then (if j = 0 then {α, 5} else {5, β})
  else if j = 0 then {α, 5} else if j = 1 then {5, 6} else if j = 2 then {6, β} else {5, β}

/-- **The forced chain along a blocking arm.** This is the induction along an arm of *unbounded*
length that turns `Monophilic.gArmLists` from a witness into a proof; it is presentation, not
mathematics, and mirrors `Monophilic.armBlockLists_forced` with the auxiliary colors moved out of
the way of the four branch colors.

If the first interior vertex avoids `α` — which it must when the branch vertex carries `α` — the
coloring is forced all the way along and the last interior vertex is driven to `β`, so it cannot
avoid `β`: the arm blocks `(α, β)`, and only that pair. No hypothesis relating `α`, `β` and the
auxiliary colors is needed here; distinctness is needed only for the lists to have two elements
(`Monophilic.card_gArmLists`). -/
theorem gArmBlocks {m : ℕ} (hm : 1 ≤ m) (α β : ℕ) : ArmBlocks m (gArmLists α β m) α β := by
  intro g hg hne h0 h1 _
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · -- a single interior vertex, with the list `{α, β}`
    have hm1' : m = 1 := by omega
    subst hm1'
    have h := hg 0 (by omega)
    rw [show gArmLists α β 1 0 = ({α, β} : Finset ℕ) from by simp [gArmLists]] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have e0 := h0 (by omega)
    have e1 := h1 (by omega)
    simp only [Nat.sub_self] at e1
    tauto
  · have hmne : m ≠ 1 := by omega
    have hg0 : g 0 = 5 := by
      have h := hg 0 (by omega)
      rw [show gArmLists α β m 0 = ({α, 5} : Finset ℕ) from by
        simp only [gArmLists, if_neg hmne]; split_ifs <;> rfl] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      have := h0 (by omega)
      tauto
    by_cases hpar : m % 2 = 0
    · have hmem : ∀ j, 0 ≤ j → j < m → g j = β ∨ g j = 5 := by
        intro j _ hj
        rcases Nat.eq_zero_or_pos j with rfl | hj1
        · exact Or.inr hg0
        · have h := hg j hj
          rw [show gArmLists α β m j = ({5, β} : Finset ℕ) from by
            simp only [gArmLists, if_neg hmne, if_pos hpar,
              if_neg (show ¬ (j = 0) from by omega)]] at h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          tauto
      have h := alt_chain (p := β) (q := 5) g 0 m hmem hne hg0 (m - 1) (by omega)
      rw [if_neg (show ¬ ((m - 1) % 2 = 0) from by omega)] at h
      exact h1 (by omega) (by simpa using h)
    · have hg1 : g 1 = 6 := by
        have h := hg 1 (by omega)
        rw [show gArmLists α β m 1 = ({5, 6} : Finset ℕ) from by
          simp only [gArmLists, if_neg hmne, if_neg hpar,
            if_neg (show ¬ ((1 : ℕ) = 0) from by omega), if_true]] at h
        have hs : g 0 ≠ g 1 := by simpa using hne 0 (by omega)
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rw [hg0] at hs
        tauto
      have hg2 : g 2 = β := by
        have h := hg 2 (by omega)
        rw [show gArmLists α β m 2 = ({6, β} : Finset ℕ) from by
          simp only [gArmLists, if_neg hmne, if_neg hpar,
            if_neg (show ¬ ((2 : ℕ) = 0) from by omega),
            if_neg (show ¬ ((2 : ℕ) = 1) from by omega), if_true]] at h
        have hs : g 1 ≠ g 2 := by simpa using hne 1 (by omega)
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rw [hg1] at hs
        tauto
      have hmem : ∀ j, 2 ≤ j → j < m → g j = 5 ∨ g j = β := by
        intro j hj2 hj
        rcases Nat.lt_or_ge j 3 with hj3 | hj3
        · rw [show j = 2 from by omega]
          exact Or.inr hg2
        · have h := hg j hj
          rw [show gArmLists α β m j = ({5, β} : Finset ℕ) from by
            simp only [gArmLists, if_neg hmne, if_neg hpar,
              if_neg (show ¬ (j = 0) from by omega), if_neg (show ¬ (j = 1) from by omega),
              if_neg (show ¬ (j = 2) from by omega)]] at h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          tauto
      have h := alt_chain (p := 5) (q := β) g 2 m hmem hne hg2 (m - 3) (by omega)
      rw [if_pos (show (m - 3) % 2 = 0 from by omega),
        show 2 + (m - 3) = m - 1 from by omega] at h
      exact h1 (by omega) h

/-- Every list of `Monophilic.gArmLists` has two colors, as soon as the two branch colors are
distinct and differ from the two auxiliary colors `5` and `6`. -/
theorem card_gArmLists {α β : ℕ} (hab : α ≠ β) (ha5 : α ≠ 5) (hb5 : β ≠ 5) (hb6 : β ≠ 6)
    (m j : ℕ) : (gArmLists α β m j).card = 2 := by
  simp only [gArmLists]
  split_ifs <;>
    first
      | exact Finset.card_pair hab
      | exact Finset.card_pair ha5
      | exact Finset.card_pair (Ne.symm hb5)
      | exact Finset.card_pair (Ne.symm hb6)
      | exact Finset.card_pair (by omega)

/-! ### The witness assignment, read on indices

`R i m j` is the list at position `j` of arm `i`, that arm having `m` interior vertices;
`Monophilic.gListsAux` walks the arms with a running offset to find which arm an index belongs
to. All of this is index bookkeeping. -/

/-- The lists on the interior vertices, as a function of the vertex index: walk the arms keeping a
running offset until the index falls inside one. The value on `[]` is never reached from
`Monophilic.gBadListAt`, which peels off the two branch vertices first. -/
def gListsAux (R : ℕ → ℕ → ℕ → Finset ℕ) : List ℕ → ℕ → ℕ → ℕ → Finset ℕ
  | [], _, _, _ => {5, 6}
  | k :: ks, i, o, v =>
      if v < o + (k - 1) then R i (k - 1) (v - o)
      else gListsAux R ks (i + 1) (o + (k - 1)) v

/-- **The lookup lemma**: position `j` of arm `i` really does receive `R i (kᵢ - 1) j`. -/
theorem gListsAux_apply (R : ℕ → ℕ → ℕ → Finset ℕ) (ks : List ℕ) (i : ℕ) (hi : i < ks.length)
    (i₀ o j : ℕ) (hj : j < ks[i] - 1) :
    gListsAux R ks i₀ o (o + gsize (ks.take i) + j) = R (i₀ + i) (ks[i] - 1) j := by
  induction ks generalizing i i₀ o with
  | nil => simp at hi
  | cons k ks ih =>
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero] at hj ⊢
          simp only [List.take_zero, gsize_nil, Nat.add_zero, gListsAux,
            if_pos (show o + j < o + (k - 1) from by omega)]
          simp only [Nat.add_sub_cancel_left]
      | succ i =>
          have hi' : i < ks.length := by simpa using hi
          simp only [List.getElem_cons_succ] at hj ⊢
          simp only [List.take_succ_cons, gsize_cons, gListsAux,
            if_neg (show ¬ (o + ((k - 1) + gsize (ks.take i)) + j < o + (k - 1)) from by omega)]
          rw [show o + ((k - 1) + gsize (ks.take i)) + j
                = o + (k - 1) + gsize (ks.take i) + j from by omega,
            ih i hi' (i₀ + 1) (o + (k - 1)) hj]
          congr 1
          omega

/-- Every list produced by `Monophilic.gListsAux` has two colors, provided `R`'s do. -/
theorem card_gListsAux {R : ℕ → ℕ → ℕ → Finset ℕ} (hR : ∀ i m j, (R i m j).card = 2)
    (ks : List ℕ) (i o v : ℕ) : (gListsAux R ks i o v).card = 2 := by
  induction ks generalizing i o with
  | nil => exact Finset.card_pair (by omega)
  | cons k ks ih =>
      simp only [gListsAux]
      split_ifs
      · exact hR _ _ _
      · exact ih _ _

/-- **The witness list assignment on `Θ(k₁, …, k_n)`**, read as a function of the vertex index:
the two branch vertices — the two largest indices — get `LS` and `LT`, and the interior of arm `i`
gets the lists `R i (kᵢ - 1)`. -/
def gBadListAt (LS LT : Finset ℕ) (R : ℕ → ℕ → ℕ → Finset ℕ) (ks : List ℕ) (v : ℕ) : Finset ℕ :=
  if v = gsize ks then LS else if v = gsize ks + 1 then LT else gListsAux R ks 0 0 v

/-- The witness list assignment on the vertices of `Θ(k₁, …, k_n)`. -/
def gBadLists (LS LT : Finset ℕ) (R : ℕ → ℕ → ℕ → Finset ℕ) (ks : List ℕ) (v : GTV ks) :
    Finset ℕ := gBadListAt LS LT R ks v.val

/-- The witness depends on a vertex only through its index. -/
theorem gBadLists_apply (LS LT : Finset ℕ) (R : ℕ → ℕ → ℕ → Finset ℕ) (ks : List ℕ)
    (v : GTV ks) : gBadLists LS LT R ks v = gBadListAt LS LT R ks v.val := rfl

/-- **The witness is a `2`-list assignment**, for every shape. -/
theorem card_gBadLists {LS LT : Finset ℕ} {R : ℕ → ℕ → ℕ → Finset ℕ} (hS : LS.card = 2)
    (hT : LT.card = 2) (hR : ∀ i m j, (R i m j).card = 2) (ks : List ℕ) (v : GTV ks) :
    (gBadLists LS LT R ks v).card = 2 := by
  simp only [gBadLists, gBadListAt]
  split_ifs
  · exact hS
  · exact hT
  · exact card_gListsAux hR _ _ _ _

/-! ### No coloring from the witness -/

/-- **The four constraints an arm imposes on a coloring**, read on indices. -/
private theorem gArm_facts {ks : List ℕ} (i : ℕ) (hi : i < ks.length) (F : ℕ → ℕ)
    (hadj : ∀ x y, x < gsize ks + 2 → y < gsize ks + 2 → x ≠ y → gAdjB ks x y = true →
      F x ≠ F y) :
    (∀ j, j + 1 < ks[i] - 1 →
        F (gsize (ks.take i) + j) ≠ F (gsize (ks.take i) + j + 1)) ∧
      (1 ≤ ks[i] - 1 → F (gsize ks) ≠ F (gsize (ks.take i) + 0)) ∧
      (1 ≤ ks[i] - 1 →
        F (gsize (ks.take i) + (ks[i] - 1 - 1)) ≠ F (gsize ks + 1)) ∧
      (ks[i] - 1 = 0 → F (gsize ks) ≠ F (gsize ks + 1)) := by
  have hle := gsize_take_add_le ks i hi
  refine ⟨fun j hj => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · exact hadj _ _ (by omega) (by omega) (by omega)
      (gAdjB_of_armStepB ks i hi _ _ (armStep_mid _ _ _ _ j hj))
  · exact hadj _ _ (by omega) (by omega) (by omega)
      (gAdjB_of_armStepB ks i hi _ _ (armStep_head _ _ _ _ (by omega)))
  · exact hadj _ _ (by omega) (by omega) (by omega)
      (gAdjB_of_armStepB ks i hi _ _ (armStep_last _ _ _ _ (by omega)))
  · refine hadj _ _ (by omega) (by omega) (by omega)
      (gAdjB_of_armStepB ks i hi _ _ ?_)
    rw [hm]
    exact armStep_direct _ _ _

/-- **The witness leaves no coloring at all**, stated entirely on indices: `F` is the would-be
coloring read through the index of a vertex. -/
private theorem gtheta_no_index_coloring {ks : List ℕ} {LS LT : Finset ℕ}
    {R : ℕ → ℕ → ℕ → Finset ℕ}
    (hblock : ∀ α ∈ LS, ∀ β ∈ LT, ∃ i, ∃ hi : i < ks.length,
      ArmBlocks (ks[i] - 1) (R i (ks[i] - 1)) α β)
    (F : ℕ → ℕ) (hmem : ∀ v, v < gsize ks + 2 → F v ∈ gBadListAt LS LT R ks v)
    (hadj : ∀ x y, x < gsize ks + 2 → y < gsize ks + 2 → x ≠ y → gAdjB ks x y = true →
      F x ≠ F y) :
    False := by
  have hα : F (gsize ks) ∈ LS := by
    have h := hmem (gsize ks) (by omega)
    rwa [show gBadListAt LS LT R ks (gsize ks) = LS from by simp [gBadListAt]] at h
  have hβ : F (gsize ks + 1) ∈ LT := by
    have h := hmem (gsize ks + 1) (by omega)
    rwa [show gBadListAt LS LT R ks (gsize ks + 1) = LT from by
      simp only [gBadListAt, if_neg (show ¬ (gsize ks + 1 = gsize ks) from by omega)]
      simp] at h
  obtain ⟨i, hi, hblk⟩ := hblock _ hα _ hβ
  have hle := gsize_take_add_le ks i hi
  obtain ⟨s1, s2, s3, s4⟩ := gArm_facts i hi F hadj
  refine hblk (fun j => F (gsize (ks.take i) + j)) ?_ s1 (fun hm => Ne.symm (s2 hm)) s3 s4
  intro j hj
  have h := hmem (gsize (ks.take i) + j) (by omega)
  rwa [show gBadListAt LS LT R ks (gsize (ks.take i) + j) = R i (ks[i] - 1) j from by
    simp only [gBadListAt, if_neg (show ¬ (gsize (ks.take i) + j = gsize ks) from by omega),
      if_neg (show ¬ (gsize (ks.take i) + j = gsize ks + 1) from by omega)]
    simpa using gListsAux_apply R ks i hi 0 0 j hj] at h

/-- **Blocking every branch pair leaves no coloring.** If for each `(α, β) ∈ LS × LT` some arm
blocks `(α, β)`, then `Θ(k₁, …, k_n)` has no coloring at all from the witness. -/
theorem gcol_gBadLists_eq_zero {ks : List ℕ} {LS LT : Finset ℕ} {R : ℕ → ℕ → ℕ → Finset ℕ}
    (hblock : ∀ α ∈ LS, ∀ β ∈ LT, ∃ i, ∃ hi : i < ks.length,
      ArmBlocks (ks[i] - 1) (R i (ks[i] - 1)) α β) :
    (gtheta ks).col (gBadLists LS LT R ks) = 0 := by
  rw [col_eq_zero_iff]
  intro f hmem hproper
  have hn : 0 < gsize ks + 2 := by omega
  refine gtheta_no_index_coloring hblock
    (fun v => f ⟨v % (gsize ks + 2), Nat.mod_lt v hn⟩) ?_ ?_
  · intro v hv
    have hEq : (⟨v % (gsize ks + 2), Nat.mod_lt v hn⟩ : GTV ks) = ⟨v, hv⟩ :=
      Fin.val_injective (Nat.mod_eq_of_lt hv)
    simp only [hEq]
    exact hmem ⟨v, hv⟩
  · intro x y hx hy hxy hB
    have hEx : (⟨x % (gsize ks + 2), Nat.mod_lt x hn⟩ : GTV ks) = ⟨x, hx⟩ :=
      Fin.val_injective (Nat.mod_eq_of_lt hx)
    have hEy : (⟨y % (gsize ks + 2), Nat.mod_lt y hn⟩ : GTV ks) = ⟨y, hy⟩ :=
      Fin.val_injective (Nat.mod_eq_of_lt hy)
    simp only [hEx, hEy]
    exact hproper (show (gtheta ks).Adj ⟨x, hx⟩ ⟨y, hy⟩ from
      ⟨fun hc => hxy (congrArg Fin.val hc), Or.inl hB⟩)

/-- **Blocking every branch pair defeats `2`-choosability.** -/
theorem not_choosable_two_gtheta {ks : List ℕ} {LS LT : Finset ℕ} {R : ℕ → ℕ → ℕ → Finset ℕ}
    (hS : LS.card = 2) (hT : LT.card = 2) (hR : ∀ i m j, (R i m j).card = 2)
    (hblock : ∀ α ∈ LS, ∀ β ∈ LT, ∃ i, ∃ hi : i < ks.length,
      ArmBlocks (ks[i] - 1) (R i (ks[i] - 1)) α β) :
    ¬ (gtheta ks).Choosable 2 := by
  intro h
  have hpos := h (gBadLists LS LT R ks) (card_gBadLists hS hT hR ks)
  rw [gcol_gBadLists_eq_zero hblock] at hpos
  exact absurd hpos (lt_irrefl 0)

/-! ### Four arms are enough

With `n ≥ 4` arms there are more arms than there are branch pairs to block, so no parity
juggling is needed — in contrast with three arms, where `Monophilic.ThetaClass` must play the
first arm's parity against the other two. Two role assignments cover every valid shape:

* `Monophilic.roleA`, used when all of the first four arms have length `≥ 2`: the branch lists
  `{1, 2}` and `{3, 4}` are disjoint, and the four arms block the four pairs one apiece;
* `Monophilic.roleB`, used when the first arm is a single edge: the branch lists `{1, 2}` and
  `{2, 3}` overlap, the single edge blocks `(2, 2)`, and the three remaining arms — which must have
  length `≥ 2`, since at most one arm is a single edge — block `(1, 2)`, `(1, 3)` and `(2, 3)`. -/

/-- The witness roles when the first four arms all have an interior vertex: they block the four
pairs of `{1, 2} × {3, 4}`, and any further arm gets the inert list `{5, 6}`. -/
def roleA (i m j : ℕ) : Finset ℕ :=
  if i = 0 then gArmLists 1 3 m j
  else if i = 1 then gArmLists 1 4 m j
  else if i = 2 then gArmLists 2 3 m j
  else if i = 3 then gArmLists 2 4 m j
  else {5, 6}

/-- The witness roles when the first arm is a single edge: it blocks `(2, 2)` by itself, and arms
`1, 2, 3` block the remaining pairs of `{1, 2} × {2, 3}`. -/
def roleB (i m j : ℕ) : Finset ℕ :=
  if i = 1 then gArmLists 1 2 m j
  else if i = 2 then gArmLists 1 3 m j
  else if i = 3 then gArmLists 2 3 m j
  else {5, 6}

/-- `Monophilic.roleA` is a `2`-list assignment: its four blocking pairs are drawn from
`{1, 2} × {3, 4}`, so both colors differ from each other and from the auxiliary `5` and `6`. -/
theorem card_roleA : ∀ i m j, (roleA i m j).card = 2 := by
  intro i m j
  simp only [roleA]
  split_ifs <;>
    first
      | exact card_gArmLists (by omega) (by omega) (by omega) (by omega) _ _
      | exact Finset.card_pair (by omega)

/-- `Monophilic.roleB` is a `2`-list assignment: its three blocking pairs `(1,2)`, `(1,3)`,
`(2,3)` have distinct entries, both differing from the auxiliary `5` and `6`. -/
theorem card_roleB : ∀ i m j, (roleB i m j).card = 2 := by
  intro i m j
  simp only [roleB]
  split_ifs <;>
    first
      | exact card_gArmLists (by omega) (by omega) (by omega) (by omega) _ _
      | exact Finset.card_pair (by omega)

/-- **No generalized theta with `n ≥ 4` arms is `2`-choosable.** The hypotheses say exactly that
the shape is that of a simple graph with at least four arms: every arm has length `≥ 1` and at
most one — necessarily the first, but no ordering is assumed beyond that — has length `1`. -/
theorem not_choosable_two_gtheta_of_four {ks : List ℕ} (hn : 4 ≤ ks.length)
    (h1 : 1 ≤ ks[0]'(by omega)) (h2 : ∀ i, ∀ hi : i < ks.length, 1 ≤ i → 2 ≤ ks[i]) :
    ¬ (gtheta ks).Choosable 2 := by
  have e0 : (0 : ℕ) < ks.length := by omega
  have e1 : (1 : ℕ) < ks.length := by omega
  have e2 : (2 : ℕ) < ks.length := by omega
  have e3 : (3 : ℕ) < ks.length := by omega
  have m1 : 1 ≤ ks[1] - 1 := by have := h2 1 e1 (by omega); omega
  have m2 : 1 ≤ ks[2] - 1 := by have := h2 2 e2 (by omega); omega
  have m3 : 1 ≤ ks[3] - 1 := by have := h2 3 e3 (by omega); omega
  rcases Nat.lt_or_ge ks[0] 2 with hk0 | hk0
  · -- the first arm is the single edge joining the two branch vertices
    have hm0 : ks[0] - 1 = 0 := by omega
    refine not_choosable_two_gtheta (LS := {1, 2}) (LT := {2, 3}) (R := roleB)
      (by decide) (by decide) card_roleB ?_
    intro α hα β hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact ⟨1, e1, gArmBlocks m1 1 2⟩
    · exact ⟨2, e2, gArmBlocks m2 1 3⟩
    · refine ⟨0, e0, ?_⟩
      rw [hm0]
      exact armBlocks_direct _ 2
    · exact ⟨3, e3, gArmBlocks m3 2 3⟩
  · -- every one of the first four arms has an interior vertex
    have m0 : 1 ≤ ks[0] - 1 := by omega
    refine not_choosable_two_gtheta (LS := {1, 2}) (LT := {3, 4}) (R := roleA)
      (by decide) (by decide) card_roleA ?_
    intro α hα β hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact ⟨0, e0, gArmBlocks m0 1 3⟩
    · exact ⟨1, e1, gArmBlocks m1 1 4⟩
    · exact ⟨2, e2, gArmBlocks m2 2 3⟩
    · exact ⟨3, e3, gArmBlocks m3 2 4⟩

/-! ### The classification -/

/-- A **valid, normalized** shape for a generalized theta graph: at least three arms, sorted, every
arm of length `≥ 1`, and at most one arm of length `1` — two would collapse to the same edge.
Sorting the arms costs nothing and, as in `Monophilic.ValidShape`, lets "at most one arm of length
one" be said as "every arm but the first has length `≥ 2`". -/
def ValidArms (ks : List ℕ) : Prop :=
  3 ≤ ks.length ∧ ks.Pairwise (· ≤ ·) ∧ (∀ i, ∀ hi : i < ks.length, 1 ≤ ks[i]) ∧
    (∀ i, ∀ hi : i < ks.length, 1 ≤ i → 2 ≤ ks[i])

/-- **Rubin's shape**, in normalized form: three arms of lengths `2`, `2` and `2m`. -/
def GoodArms (ks : List ℕ) : Prop := ∃ m, 1 ≤ m ∧ ks = [2, 2, 2 * m]

/-- A normalized three-arm shape, from the three inequalities of `Monophilic.ValidShape`. -/
theorem validArms_triple {a b c : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hb : 2 ≤ b) :
    ValidArms [a, b, c] := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
    refine ⟨?_, ?_, by simp⟩
    · rintro x (rfl | rfl | h) <;> first | omega | simp at h
    · rintro x (rfl | h) <;> first | omega | simp at h
  · intro i hi
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by
      simp only [List.length_cons, List.length_nil] at hi; omega
    rcases hi3 with rfl | rfl | rfl <;> simp <;> omega
  · intro i hi h1
    have hi3 : i = 1 ∨ i = 2 := by
      simp only [List.length_cons, List.length_nil] at hi; omega
    rcases hi3 with rfl | rfl <;> simp <;> omega

/-- A three-arm valid shape is a valid three-arm shape in the sense of
`Monophilic.ValidShape`. -/
private theorem validShape_of_validArms {a b c : ℕ} (hv : ValidArms [a, b, c]) :
    ValidShape a b c := by
  obtain ⟨-, hs, h1, h2⟩ := hv
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil] at hs
  refine ⟨by simpa using h1 0 (by simp), ?_, ?_, by simpa using h2 1 (by simp) (by omega)⟩
  · exact hs.1 b (by simp)
  · exact hs.2.1 c (by simp)

/-- **The classification of `2`-choosable generalized theta graphs.** A generalized theta with
`n ≥ 3` arms is `2`-choosable exactly when `n = 3` and its arms have lengths `2`, `2` and `2m`.

This is a component of Rubin's theorem (Erdős–Rubin–Taylor 1980); see the module docstring. The
three-arm case is `Monophilic.choosable_two_thetaGen_iff`, transported along
`Monophilic.choosable_gtheta_triple_iff`; the arity-`≥ 4` case is
`Monophilic.not_choosable_two_gtheta_of_four`. -/
theorem choosable_two_gtheta_iff {ks : List ℕ} (hv : ValidArms ks) :
    (gtheta ks).Choosable 2 ↔ GoodArms ks := by
  constructor
  · intro hch
    obtain ⟨hlen, hs, h1, h2⟩ := hv
    rcases Nat.lt_or_ge ks.length 4 with hsmall | hbig
    · -- three arms: transport to `thetaGen` and quote the three-arm classification
      obtain ⟨a, b, c, rfl⟩ : ∃ a b c, ks = [a, b, c] := by
        match ks, hlen, hsmall with
        | [a, b, c], _, _ => exact ⟨a, b, c, rfl⟩
      have hvs : ValidShape a b c := validShape_of_validArms ⟨hlen, hs, h1, h2⟩
      obtain ⟨ha, hab, hbc, hb2⟩ := hvs
      have hgood : GoodShape a b c :=
        (choosable_two_thetaGen_iff ⟨ha, hab, hbc, hb2⟩).mp
          ((choosable_gtheta_triple_iff ha (by omega) (by omega) 2).mp hch)
      obtain ⟨rfl, rfl, hc⟩ := hgood
      obtain ⟨r, hr⟩ := hc
      exact ⟨r, by omega, by rw [show c = 2 * r from by omega]⟩
    · exact absurd hch (not_choosable_two_gtheta_of_four hbig
        (h1 0 (by omega)) (fun i hi hi1 => h2 i hi hi1))
  · rintro ⟨m, hm, rfl⟩
    exact (choosable_gtheta_triple_iff (by omega) (by omega) (by omega) 2).mpr
      (choosable_two_thetaGen_two_two m hm)

/-! ### Numerical checks

Every claim above was checked by brute force on concrete shapes before it was proved. The witness
of `Monophilic.gWitness` is `Monophilic.gBadLists` with `Monophilic.roleB` when the first arm is a
single edge and `Monophilic.roleA` otherwise, exactly as
`Monophilic.not_choosable_two_gtheta_of_four` chooses; `Monophilic.gWitnessCheck` verifies that it
is a `2`-list assignment with no coloring at all, and the sweep below runs it over *every* sorted
valid shape with four or five arms and total length at most `12`. -/

section Guards

/-- The witness `2`-list assignment used by `Monophilic.not_choosable_two_gtheta_of_four`. -/
def gWitness (ks : List ℕ) : GTV ks → Finset ℕ :=
  if ks.headI = 1 then gBadLists {1, 2} {2, 3} roleB ks else gBadLists {1, 2} {3, 4} roleA ks

/-- The whole check, for one shape: the witness has two colors at every vertex and
`Θ(k₁, …, k_n)` has no coloring from it at all. -/
def gWitnessCheck (ks : List ℕ) : Bool :=
  decide (∀ v : GTV ks, (gWitness ks v).card = 2) && ((gtheta ks).col (gWitness ks) == 0)

/-- All sorted shapes with `n` arms, total length at most `s`, and at most one arm of length
one. -/
def gShapes (n s : ℕ) : List (List ℕ) :=
  let rec go : ℕ → ℕ → ℕ → List (List ℕ)
    | 0, _, _ => [[]]
    | j + 1, lo, budget =>
        ((List.range (budget + 1)).filter (fun k => lo ≤ k)).flatMap fun k =>
          (go j (max k 2) (budget - k)).map fun t => k :: t
  go n 1 s

#guard (gShapes 4 12).length = 28
#guard (gShapes 5 12).length = 11
#guard (gShapes 3 8) = [[1, 2, 2], [1, 2, 3], [1, 2, 4], [1, 2, 5], [1, 3, 3], [1, 3, 4],
  [2, 2, 2], [2, 2, 3], [2, 2, 4], [2, 3, 3]]

-- **The sweep.** Every sorted valid shape with four or five arms and total length at most `12`.
#guard (gShapes 4 12).all gWitnessCheck
#guard (gShapes 5 12).all gWitnessCheck

-- A few larger ones, past the range of the sweep.
#guard gWitnessCheck [2, 2, 2, 6]
#guard gWitnessCheck [4, 4, 4, 4]
#guard gWitnessCheck [2, 2, 5, 5]
#guard gWitnessCheck [1, 2, 2, 3, 3]

-- The witness never fires on **three** arms: with three arms only three of the four branch pairs
-- get blocked, which is why arity `3` needs the parity argument of `Monophilic.ThetaClass`.
#guard (gShapes 3 10).all fun ks => !gWitnessCheck ks

-- `Θ(2, 2, 2m)` really is different: it has colorings from the constant `2`-list assignment, and
-- from the witness too.
#guard (gtheta [2, 2, 2]).colConst 2 = 2
#guard (gtheta [2, 2, 4]).colConst 2 = 2
#guard (gtheta [2, 2, 2, 2]).colConst 2 = 2
#guard (gtheta [2, 2, 2, 2]).col (gWitness [2, 2, 2, 2]) = 0

end Guards

/-! ### `K_{2,4}` is not `2`-choosable, via the arity-four case

`SimpleGraph.ERT.K 2 = K_{2,4}` is the smallest Erdős–Rubin–Taylor example, and it is exactly
`Θ(2, 2, 2, 2)`: the two left vertices are the branch vertices and the four right vertices are the
four arms' single interior vertices. `Monophilic.not_choosable_two_gtheta_of_four` therefore
reproves `SimpleGraph.ERT.not_choosable 2` by a different route — the arms' lists here are
`{1,3}, {1,4}, {2,3}, {2,4}` against branch lists `{1,2}` and `{3,4}`, which is the ERT
transversal construction with the colors renamed. The two proofs agree, as they must. -/

/-- `Θ(2, 2, 2, 2)` sits inside `K_{2,4}`: the two branch vertices go to the left side and the
four interior vertices to the four transversal-indexing functions. It is in fact a bijection. -/
def K24Map (v : GTV [2, 2, 2, 2]) : Fin 2 ⊕ (Fin 2 → Fin 2) :=
  if v.val = 4 then Sum.inl 0
  else if v.val = 5 then Sum.inl 1
  else Sum.inr (fun i => if i = 0 then (if v.val < 2 then 0 else 1)
                         else (if v.val % 2 = 0 then 0 else 1))

/-- The map onto `K_{2,4}` is injective — six vertices, checked one pair at a time. Bookkeeping,
not mathematics. -/
theorem K24Map_injective : Function.Injective K24Map := by decide

/-- The map onto `K_{2,4}` carries edges to edges — again a finite check. Bookkeeping, not
mathematics. -/
theorem K24Map_adj (u v : GTV [2, 2, 2, 2]) (h : (gtheta [2, 2, 2, 2]).Adj u v) :
    (ERT.K 2).Adj (K24Map u) (K24Map v) := by revert u v; decide

/-- **`K_{2,4}` is not `2`-choosable**, obtained from the arity-four case of the classification of
generalized theta graphs. This is the Erdős–Rubin–Taylor example, and `SimpleGraph.ERT.not_choosable
2` proves the same statement from the transversal list assignment `L₀` directly; the two routes
agree. -/
theorem not_choosable_two_K24 : ¬ (ERT.K 2).Choosable 2 := fun h =>
  not_choosable_two_gtheta_of_four (ks := [2, 2, 2, 2]) (by decide) (by decide)
      (by decide)
    (Choosable.comap h K24Map_injective K24Map_adj)

/-- The cross-check: the Erdős–Rubin–Taylor proof of the same statement. -/
example : ¬ (ERT.K 2).Choosable 2 := ERT.not_choosable 2

-- and the two graphs really are the same one, on the counts a graph this small is pinned down by
#guard Fintype.card (GTV [2, 2, 2, 2]) = Fintype.card (Fin 2 ⊕ (Fin 2 → Fin 2))
#guard (gtheta [2, 2, 2, 2]).edgeFinset.card = (ERT.K 2).edgeFinset.card
#guard (gtheta [2, 2, 2, 2]).colConst 2 = (ERT.K 2).colConst 2
#guard (gtheta [2, 2, 2, 2]).colConst 3 = (ERT.K 2).colConst 3
#guard (gtheta [2, 2, 2, 2]).colConst 4 = (ERT.K 2).colConst 4

/-! ### Cross-checks

The general theorem specializes to the shapes settled elsewhere in the library. -/

section Examples

/-- `K_{2,4} = Θ(2,2,2,2)`, the smallest arity-four obstruction. -/
example : ¬ (gtheta [2, 2, 2, 2]).Choosable 2 :=
  not_choosable_two_gtheta_of_four (by decide) (by decide) (by decide)

/-- `K_{2,n}` is not `2`-choosable for `n ≥ 4`. -/
example : ¬ (gtheta [2, 2, 2, 2, 2]).Choosable 2 :=
  not_choosable_two_gtheta_of_four (by decide) (by decide) (by decide)

/-- `K_{2,3}` with an extra edge between the two branch vertices. -/
example : ¬ (gtheta [1, 2, 2, 2]).Choosable 2 :=
  not_choosable_two_gtheta_of_four (by decide) (by decide) (by decide)

/-- Rubin's own family, on the general model. -/
example (r : ℕ) : (gtheta [2, 2, 2 * r + 2]).Choosable 2 :=
  (choosable_two_gtheta_iff (validArms_triple (a := 2) (b := 2) (c := 2 * r + 2)
    (by omega) (by omega) (by omega) (by omega))).mpr
    ⟨r + 1, by omega, by rw [show 2 * r + 2 = 2 * (r + 1) from by omega]⟩

/-- `θ_{2,2,\text{odd}}` is not `2`-choosable, on the general model. -/
example (r : ℕ) : ¬ (gtheta [2, 2, 2 * r + 3]).Choosable 2 := by
  rw [choosable_two_gtheta_iff (validArms_triple (a := 2) (b := 2) (c := 2 * r + 3)
    (by omega) (by omega) (by omega) (by omega))]
  rintro ⟨m, hm, hk⟩
  simp only [List.cons.injEq] at hk
  omega

end Examples

end Monophilic

#print axioms Monophilic.gsize_take_succ
#print axioms Monophilic.gAdjAux_of_armStepB
#print axioms Monophilic.gAdjB_triple
#print axioms Monophilic.choosable_gtheta_triple_iff
#print axioms Monophilic.armBlocks_direct
#print axioms Monophilic.gArmBlocks
#print axioms Monophilic.card_gArmLists
#print axioms Monophilic.gListsAux_apply
#print axioms Monophilic.card_gBadLists
#print axioms Monophilic.gcol_gBadLists_eq_zero
#print axioms Monophilic.not_choosable_two_gtheta
#print axioms Monophilic.not_choosable_two_gtheta_of_four
#print axioms Monophilic.choosable_two_gtheta_iff
#print axioms Monophilic.K24Map_injective
#print axioms Monophilic.K24Map_adj
#print axioms Monophilic.not_choosable_two_K24
