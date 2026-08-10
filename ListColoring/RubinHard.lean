/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Rubin
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Rubin's theorem: the hard direction

`ListColoring.Rubin` proves the easy direction of Rubin's characterization — every graph on Rubin's
list is `2`-choosable — and isolates the hard direction

> a `2`-choosable connected graph has a single vertex, an even cycle or `θ_{2,2,2m}` for its core

as the one thing still to be proved. This file attacks that direction. Contrapositively, a
connected graph `H` of minimum degree `≥ 2` which is none of the three fails to be `2`-choosable
because:

1. if `H` has an odd cycle it is not even `2`-colorable, and choosability passes to subgraphs;
2. otherwise `H` is bipartite, and some structural alternative applies. Every formulation of this
   step attempted *in this repository* was false (see the correction section below); the one that
   works is **Rubin's own**, and it is now proved — `ListColoring.rubin_structure`;
3. a generalized theta `Θ(k₁,…,k_n)` is `2`-choosable exactly when `n = 3` and the lengths are
   `(2, 2, \text{even})` (`ListColoring.choosable_two_gtheta_iff`, **proved**, arity arbitrary), and
   a **dumbbell** — two cycles joined by a path — is not `2`-choosable
   (`ListColoring.not_choosable_two_of_dumbbell`, **proved**).

Step 2 as previously written here claimed that a bipartite `H` with a vertex of degree `≥ 3`
contains a generalized theta subgraph. That is **false**: two `4`-cycles glued at a single vertex
satisfies the hypotheses and contains no generalized theta of any arity. It is also the wrong shape
of claim even where true, since containing a *good* theta implies nothing.

Step 2 is the missing structural ingredient (Mathlib has no block or ear decomposition), and its
"three arms" version is *not enough*: `K_{2,4}` — this development's own `SimpleGraph.ERT.K 2` — is
a connected bipartite graph of minimum degree `2`, not a cycle and not a `θ_{2,2,2m}`, whose only
three-arm theta subgraph is the *good* `θ_{2,2,2}`, and which is nevertheless not `2`-choosable. It
is the generalized theta with four arms of length two. See the section "A removed definition, and
why it must stay removed" below, which records the brute-force refutation of the three-arm form.

Everything else is developed here: general theta graphs, explicit `2`-list assignments with no
coloring at all for the excluded shapes, and the transfer of non-choosability along subgraphs.

## General theta graphs

The repository's `ListColoring.theta m` is hardwired as `θ_{2,2,2m}`. `ListColoring.thetaGen a b c`
is the general theta graph, on the vertex type `Fin (a + b + c - 1)`: the interior vertices of the
three arms occupy the initial blocks of length `a - 1`, `b - 1`, `c - 1`, and the two branch
vertices are the last two indices. It really is a theta graph — `a + b + c - 1` vertices,
`a + b + c` edges, two vertices of degree three and the rest of degree two — as the `#guard`s
below record, and for the shape `(2, 2, 2m)` it agrees with `ListColoring.theta m` on the counts
`col(·, n)`.

## The obstructions

Non-`2`-choosability is certified by an explicit `2`-list assignment with **no** coloring; each is
checked by brute force with `#guard` before it is used. One construction,
`ListColoring.thetaBadLists`, covers every shape at once. Give both branch vertices the list
`{1, 2}`; then a coloring is a choice of a pair `(α, β) ∈ {1,2} × {1,2}` at the branch vertices
together with a coloring of each arm's interior, and an arm *blocks* `(α, β)` when its lists leave
no interior coloring compatible with `α` and `β`. An arm with all lists `{1, 2}` blocks two pairs,
`(1,1)` and `(2,2)` if it has odd length and `(1,2)`, `(2,1)` if even; an arm of length `≥ 3` can
be made to block any single prescribed pair, by starting with the list `{α, 3}` and propagating a
forced chain to `β` through the auxiliary colors `3` and `4`. Three arms therefore kill all four
pairs as soon as *two* of them have length `≥ 3` — and for a valid shape that is exactly the case
not already settled by parity, since a shape with `b ≤ 2` other than `(2,2,\text{even})` has an
odd cycle.

The witness is verified by a `#guard` sweep over every valid shape with `a ≤ 4`, `b ≤ 4`, `c ≤ 5`;
three shapes are then turned into theorems. Only the general *proof* of the blocking argument, an
induction along an arm of unbounded length, is missing.

## Main definitions

* `ListColoring.thetaGen` : the general theta graph `θ_{a,b,c}`
* `ListColoring.Contains` : `G` contains a copy of `K` as a subgraph
* `ListColoring.armBlockLists`, `ListColoring.thetaBadLists` : the general witness assignment
* `ListColoring.ValidShape`, `ListColoring.GoodShape` : normalized theta shapes, and Rubin's shape
* `ListColoring.ThetaClassification` : the classification of `2`-choosable theta graphs, discharged
  in `ListColoring.ThetaClass`

## Main results

* `ListColoring.not_choosable_of_contains` : non-`2`-choosability passes from a subgraph to the
  whole graph, and `ListColoring.not_choosable_two_of_contains_odd_cycle` for an odd cycle
* `ListColoring.colConst_thetaOf_odd` : `col(θ_{2,2,k}, 2) = 0` for odd `k`, whence
  `ListColoring.not_choosable_two_thetaOf_odd` — the whole family `θ_{2,2,\text{odd}}`
* `ListColoring.not_choosable_two_thetaGen_133`, `ListColoring.not_choosable_two_thetaGen_333`,
  `ListColoring.not_choosable_two_thetaGen_244` : the three smallest *bipartite* obstructions,
  `2`-colorable but not `2`-choosable, hence also not enumeratively chromatic-choosable at `2`
* `ListColoring.not_choosable_two_of_contains_theta333` : a hypothesis-free consequence — a graph
  containing `θ_{3,3,3}` is not `2`-choosable
* `ListColoring.exists_cycle_of_two_le_degree` : a connected graph of minimum degree `≥ 2` contains
  a cycle
* `ListColoring.card_lt_card_edgeFinset` : with a vertex of degree `≥ 3` it has more edges than
  vertices, and `ListColoring.degree_eq_two_of_card_edgeFinset_le` is the converse reading
-/

open Finset

set_option maxRecDepth 40000

namespace ListColoring

open SimpleGraph

/-! ### General theta graphs

`thetaGen a b c` is laid out on `Fin (a + b + c - 1)`. Writing `A = a - 1`, `B = b - 1`,
`C = c - 1` for the numbers of interior vertices of the three arms, the indices

* `0, …, A - 1` are the interior of the first arm, in order from the first branch vertex;
* `A, …, A + B - 1` the interior of the second;
* `A + B, …, A + B + C - 1` the interior of the third;
* `A + B + C = a + b + c - 3` and `a + b + c - 2` are the two branch vertices.

An arm with no interior vertex contributes the single edge joining the two branch vertices, so
`thetaGen 1 b c` has an arm of length one. Two such arms would collapse to a single edge; that is
why `ValidShape` below allows at most one arm of length one. -/

/-- One step along an arm of a theta graph, on indices: `o` is the index of the arm's first
interior vertex, `m` the number of interior vertices it has, and `ps`, `pt` are the two branch
vertices. The arm runs `ps, o, o + 1, …, o + m - 1, pt`, and degenerates to the single edge
`ps — pt` when `m = 0`. -/
def armStepB (o m ps pt x y : ℕ) : Bool :=
  if m = 0 then (x == ps && y == pt)
  else ((x == ps && y == o) ||
        (decide (o ≤ x) && (y == x + 1) && decide (y < o + m)) ||
        (x == o + m - 1 && y == pt))

/-- Adjacency of `thetaGen a b c`, read on indices and before symmetrizing: the union of the three
arms, whose interiors start at `0`, `a - 1` and `a + b - 2`. -/
def thetaGenAdjB (a b c x y : ℕ) : Bool :=
  armStepB 0 (a - 1) (a + b + c - 3) (a + b + c - 2) x y ||
  armStepB (a - 1) (b - 1) (a + b + c - 3) (a + b + c - 2) x y ||
  armStepB (a + b - 2) (c - 1) (a + b + c - 3) (a + b + c - 2) x y

/-- The vertex type of the general theta graph `θ_{a,b,c}`: it has `a + b + c - 1` vertices. -/
abbrev TGV (a b c : ℕ) : Type := Fin (a + b + c - 1)

/-- **The general theta graph `θ_{a,b,c}`**: two branch vertices joined by three internally
disjoint paths, of lengths `a`, `b` and `c`. Compare `ListColoring.theta m`, which is the special
shape `θ_{2,2,2m}` built by coning twice over the ends of a path. -/
def thetaGen (a b c : ℕ) : SimpleGraph (TGV a b c) where
  Adj x y := x ≠ y ∧ (thetaGenAdjB a b c x.val y.val ∨ thetaGenAdjB a b c y.val x.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableRelThetaGen (a b c : ℕ) : DecidableRel (thetaGen a b c).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧
    (thetaGenAdjB a b c x.val y.val = true ∨ thetaGenAdjB a b c y.val x.val = true)))

/-! `θ_{a,b,c}` has `a + b + c - 1` vertices and `a + b + c` edges. -/

#guard Fintype.card (TGV 1 3 3) = 6
#guard Fintype.card (TGV 3 3 3) = 8
#guard Fintype.card (TGV 2 4 4) = 9
#guard (thetaGen 1 3 3).edgeFinset.card = 7
#guard (thetaGen 3 3 3).edgeFinset.card = 9
#guard (thetaGen 2 4 4).edgeFinset.card = 10
#guard (thetaGen 2 2 2).edgeFinset.card = 6
#guard (thetaGen 2 2 4).edgeFinset.card = 8
#guard (thetaGen 2 2 5).edgeFinset.card = 9
#guard (thetaGen 1 2 2).edgeFinset.card = 5
#guard (thetaGen 3 4 5).edgeFinset.card = 12
#guard Fintype.card (TGV 3 4 5) = 11

/-! Every vertex has degree `2` except the two branch vertices — the last two indices — which have
degree `3`. The sweep below checks this, together with the edge count, for every valid shape with
`a ≤ 4`, `b ≤ 4`, `c ≤ 5`. -/

#guard ((univ : Finset (TGV 3 3 3)).filter fun v => (thetaGen 3 3 3).degree v = 3).card = 2
#guard ((univ : Finset (TGV 3 3 3)).filter fun v => (thetaGen 3 3 3).degree v = 2).card = 6
#guard ((univ : Finset (TGV 2 4 4)).filter fun v => (thetaGen 2 4 4).degree v = 3).card = 2
#guard ((univ : Finset (TGV 1 3 3)).filter fun v => (thetaGen 1 3 3).degree v = 3).card = 2

/-- `θ_{a,b,c}` really is a theta graph: `a + b + c` edges, and the degree of a vertex is `3` at
the two branch vertices — the two largest indices — and `2` everywhere else. -/
def thetaGenShapeOk (a b c : ℕ) : Bool :=
  decide ((thetaGen a b c).edgeFinset.card = a + b + c ∧
    ∀ v : TGV a b c, (thetaGen a b c).degree v = if v.val + 3 < a + b + c then 2 else 3)

#guard [1, 2, 3, 4].all fun a => [2, 3, 4].all fun b => [2, 3, 4, 5].all fun c =>
  if decide (a ≤ b ∧ b ≤ c) then thetaGenShapeOk a b c else true

/-! For the shape `(2, 2, 2m)` the general construction agrees with `ListColoring.theta m` on the
counts `col(·, n)`, which for `n = 3, 4, 5` already pin down the chromatic polynomial of a graph
this small. -/

#guard Fintype.card (TGV 2 2 2) = Fintype.card (ThetaV 1)
#guard Fintype.card (TGV 2 2 4) = Fintype.card (ThetaV 2)
#guard Fintype.card (TGV 2 2 6) = Fintype.card (ThetaV 3)
#guard (thetaGen 2 2 2).colConst 2 = (theta 1).colConst 2
#guard (thetaGen 2 2 2).colConst 3 = (theta 1).colConst 3
#guard (thetaGen 2 2 2).colConst 4 = (theta 1).colConst 4
#guard (thetaGen 2 2 4).colConst 2 = (theta 2).colConst 2
#guard (thetaGen 2 2 4).colConst 3 = (theta 2).colConst 3
#guard (thetaGen 2 2 4).colConst 4 = (theta 2).colConst 4
#guard (thetaGen 2 2 6).colConst 3 = (theta 3).colConst 3

/-! A shape whose three lengths do not all have the same parity has an odd cycle, so it is not even
`2`-colorable. For the family `(2, 2, \text{odd})` this is `ListColoring.colConst_thetaOf_odd` below,
proved for all lengths at once on the model `ListColoring.thetaOf`. -/

#guard (thetaGen 2 2 3).colConst 2 = 0
#guard (thetaGen 2 2 5).colConst 2 = 0
#guard (thetaGen 1 2 2).colConst 2 = 0
#guard (thetaGen 1 2 4).colConst 2 = 0
#guard (thetaGen 2 3 4).colConst 2 = 0

/-! ### Non-choosability passes to supergraphs -/

/-- `G` **contains** a copy of `K`: an injection of the vertices of `K` into those of `G` carrying
edges to edges. Only a *subgraph* is asked for, not an induced one, which is all that a
choosability argument ever needs. -/
def Contains {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ a b, K.Adj a b → G.Adj (f a) (f b)

/-- A graph contains itself. -/
theorem contains_self {V : Type*} (G : SimpleGraph V) : Contains G G :=
  ⟨id, Function.injective_id, fun _ _ h => h⟩

/-- **Non-choosability passes from a subgraph to the whole graph**: this is
`SimpleGraph.Choosable.comap` read contrapositively. -/
theorem not_choosable_of_contains {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj] {K : SimpleGraph W}
    [DecidableRel K.Adj] {n : ℕ} (hK : ¬ K.Choosable n) (h : Contains G K) : ¬ G.Choosable n := by
  obtain ⟨f, hf, hadj⟩ := h
  exact fun hG => hK (hG.comap hf hadj)

/-- A graph that is not `n`-colorable is not `n`-choosable, since `χ(G) ≤ χ_ℓ(G)`. -/
theorem not_choosable_of_not_colorable {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} (h : ¬ G.Colorable n) : ¬ G.Choosable n :=
  fun hc => h (colorable_of_choosable hc)

/-- **A graph containing an odd cycle is not `2`-choosable.** `closePath k` has `k + 1` vertices,
so `Even k` picks out the cycles on an odd number of them. This is step 1 of the contrapositive:
an odd cycle is not `2`-colorable (`ListColoring.not_choosable_two_closePath_of_even`) and
non-choosability travels upwards along subgraphs. -/
theorem not_choosable_two_of_contains_odd_cycle {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k)
    (h : Contains G (closePath k)) : ¬ G.Choosable 2 :=
  not_choosable_of_contains (not_choosable_two_closePath_of_even hk hk2) h

/-! ### `θ_{2,2,k}` for odd `k`

`ListColoring.thetaOf k` — a path of length `k` with two extra vertices, each joined to both of its
ends — *is* the theta graph `θ_{2,2,k}`. For odd `k` it contains the odd cycle made of the long
path and one of the two short arms, and indeed it has no coloring at all from the constant list of
size two. The computation is the one behind `ListColoring.colConst_thetaOf`, with the even chain
`ListColoring.col_chain_const` replaced by its odd counterpart. -/

/-- **The alternating chain, odd length.** With every list equal to `{x, y}` and the color `x`
prescribed at both ends of a path of *odd* length, there is no coloring at all: the colors are
forced to alternate and arrive at the far end already equal to `x`. Compare
`ListColoring.col_chain_const`, which finds exactly one coloring in the even case. -/
theorem col_chain_const_odd (P : Finset ℕ) (x y : ℕ) (hxy : x ≠ y) (hP : P = {x, y}) :
    ∀ r : ℕ, (pathG (2 * r + 1)).col (levelAssign (2 * r + 1) (fun _ => P) {x} {x}) = 0
  | 0 => by
      show (pathG 1).col (levelAssign 1 (fun _ => P) {x} {x}) = 0
      rw [col_levelAssign_one, Finset.sum_singleton, Finset.erase_singleton, Finset.card_empty]
  | r + 1 =>
      (col_levelAssign_two_step (2 * r) (fun _ => P) {x} hxy hP hP).trans
        (col_chain_const_odd P x y hxy hP r)

/-- **`col(θ_{2,2,k}, 2) = 0` for odd `k`.** Peeling the two apexes leaves four terms; in two of
them a terminal vertex of the long path is left with no color at all, and in the other two the
forced alternating chain along a path of odd length arrives at the far end with the color it
started from. -/
theorem colConst_thetaOf_odd (r : ℕ) : (thetaOf (2 * r + 1)).colConst 2 = 0 := by
  have hconst : (constList (Option (Option (PathV (2 * r + 1)))) 2)
      = thetaAssign (2 * r + 1) (range 2) (range 2)
          (levelAssign (2 * r + 1) (fun _ => range 2) (range 2) (range 2)) := by
    rw [levelAssign_const]
    funext v
    cases v with
    | none => rfl
    | some u => cases u <;> rfl
  rw [colConst, hconst, col_thetaOf_thetaAssign]
  simp only [eraseEnds_levelAssign, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show ((range 2).erase 0).erase 0 = ({1} : Finset ℕ) from by decide,
    show ((range 2).erase 0).erase 1 = (∅ : Finset ℕ) from by decide,
    show ((range 2).erase 1).erase 0 = (∅ : Finset ℕ) from by decide,
    show ((range 2).erase 1).erase 1 = ({0} : Finset ℕ) from by decide,
    col_chain_const_odd (range 2) 1 0 (by decide) (by decide) r,
    col_levelAssign_eq_zero_of_head,
    col_chain_const_odd (range 2) 0 1 (by decide) (by decide) r]
  decide

/-- **`θ_{2,2,k}` is not `2`-colorable for odd `k`**: it contains the odd cycle formed by the long
path and one of the two arms of length two. -/
theorem not_colorable_two_thetaOf_odd (r : ℕ) : ¬ (thetaOf (2 * r + 1)).Colorable 2 :=
  colConst_eq_zero_iff_not_colorable.mp (colConst_thetaOf_odd r)

/-- **`θ_{2,2,k}` is not `2`-choosable for odd `k`.** Together with
`ListColoring.choosable_theta` this pins down exactly which of the graphs `θ_{2,2,k}` belong to
Rubin's list: those with `k` even. -/
theorem not_choosable_two_thetaOf_odd (r : ℕ) : ¬ (thetaOf (2 * r + 1)).Choosable 2 :=
  not_choosable_of_not_colorable (not_colorable_two_thetaOf_odd r)

/-! ### The bipartite obstructions

The shapes above are excluded already by the chromatic number. The interesting obstructions are
the *bipartite* ones — `2`-colorable, yet not `2`-choosable — and the smallest are `θ_{1,3,3}`,
`θ_{3,3,3}` and `θ_{2,4,4}`.

One assignment covers every shape at once. Both branch vertices get the list `{1, 2}`, so a
coloring amounts to a pair `(α, β) ∈ {1,2} × {1,2}` of branch colors together with a coloring of
each arm's interior; an arm *blocks* `(α, β)` when its lists leave no interior coloring compatible
with `α` and `β`. If two of the three arms have length `≥ 3` — which, for a valid shape, is
exactly the situation not already settled by parity — then:

* the remaining arm carries the constant lists `{1, 2}`, forcing its interior to alternate, and
  blocks `(1,1)` and `(2,2)` if it has odd length, `(1,2)` and `(2,1)` if even;
* each of the two long arms blocks one of the two surviving pairs. To block `(α, β)` it starts
  with the list `{α, 3}`, so that `α` forces the color `3`, and then propagates a forced chain to
  `β`: alternating `3, β, 3, …` when the number of interior vertices is even, and
  `3, 4, β, 3, β, …` when it is odd, the detour through `4` fixing the parity.

All four pairs are therefore blocked and no coloring exists at all. Both the construction and each
`col = 0` are checked by brute force with `#guard` before anything is proved from them, and the
sweep below runs the check over every valid shape with `a ≤ 4`, `b ≤ 4` and `c ≤ 5`. -/

/-- The lists along an arm with `m` interior vertices which blocks the pair `(α, β)` of branch
colors: `j` is the position along the arm, counted from the branch vertex carrying `α`. The chain
of forced colors is `3, β, 3, …` for `m` even and `3, 4, β, 3, β, …` for `m` odd, and the list at
position `j` is the pair of forced colors at `j - 1` and `j`. Meaningful for `m ≥ 2`. -/
def armBlockLists (α β m j : ℕ) : Finset ℕ :=
  if m % 2 = 0 then (if j = 0 then {α, 3} else {3, β})
  else if j = 0 then {α, 3} else if j = 1 then {3, 4} else if j = 2 then {4, β} else {3, β}

/-- **The witness `2`-list assignment on `θ_{a,b,c}`.** For `b ≤ 2` the shape is `(a, 2, c)` with
`a ≤ 2`, which for a valid non-Rubin shape has an odd cycle, and the constant assignment `{1, 2}`
already has no coloring. Otherwise both `b` and `c` are `≥ 3`: the first arm keeps the constant
lists `{1, 2}`, and the second and third arms block, respectively, the pairs `(1, β)` and
`(2, β')` left over by the parity of the first arm. -/
def thetaBadLists (a b c : ℕ) (v : TGV a b c) : Finset ℕ :=
  if b ≤ 2 then {1, 2}
  else if v.val + 1 < a then {1, 2}
  else if v.val + 2 < a + b then
    armBlockLists 1 (if a % 2 = 1 then 2 else 1) (b - 1) (v.val + 1 - a)
  else if v.val + 3 < a + b + c then
    armBlockLists 2 (if a % 2 = 1 then 1 else 2) (c - 1) (v.val + 2 - a - b)
  else {1, 2}

/-- The number of colorings of `θ_{a,b,c}` from the witness assignment, spelled out so that the
sweep below can evaluate it. -/
def colThetaBad (a b c : ℕ) : ℕ := (thetaGen a b c).col (thetaBadLists a b c)

/-- The witness is a `2`-list assignment on `θ_{a,b,c}`, as a boolean for the sweep below. -/
def thetaBadIsTwoList (a b c : ℕ) : Bool :=
  decide (∀ v : TGV a b c, (thetaBadLists a b c v).card = 2)

/-- The whole check, for one shape: on a valid shape other than Rubin's `(2, 2, \text{even})` the
witness is a `2`-list assignment and `θ_{a,b,c}` has no coloring from it at all. -/
def thetaBadCheck (a b c : ℕ) : Bool :=
  if decide (a ≤ b ∧ b ≤ c ∧ ¬ (a = 2 ∧ b = 2 ∧ c % 2 = 0)) then
    thetaBadIsTwoList a b c && (colThetaBad a b c == 0)
  else true

-- The sweep: every valid shape with `a ≤ 4`, `b ≤ 4`, `c ≤ 5` other than `(2,2,2)` and `(2,2,4)`.
#guard [1, 2, 3, 4].all fun a => [2, 3, 4].all fun b => [2, 3, 4, 5].all fun c =>
  thetaBadCheck a b c

-- On Rubin's own shape it necessarily fails, since `θ_{2,2,2m}` *is* `2`-choosable.
#guard colThetaBad 2 2 2 = 2
#guard colThetaBad 2 2 4 = 2
#guard colThetaBad 2 2 6 = 2

-- The three smallest bipartite obstructions, and the fact that they are indeed bipartite.
#guard colThetaBad 1 3 3 = 0
#guard colThetaBad 3 3 3 = 0
#guard colThetaBad 2 4 4 = 0
#guard (thetaGen 1 3 3).colConst 2 = 2
#guard (thetaGen 3 3 3).colConst 2 = 2
#guard (thetaGen 2 4 4).colConst 2 = 2

/-- **`θ_{1,3,3}` is not `2`-choosable**, witnessed by `ListColoring.thetaBadLists`: the direct edge
blocks `(1,1)` and `(2,2)`, and the two arms of length three block `(1,2)` and `(2,1)`. -/
theorem not_choosable_two_thetaGen_133 : ¬ (thetaGen 1 3 3).Choosable 2 := by
  intro h
  have hcard : ∀ v, (thetaBadLists 1 3 3 v).card = 2 := by decide
  have hpos := h (thetaBadLists 1 3 3) hcard
  have hzero : (thetaGen 1 3 3).col (thetaBadLists 1 3 3) = 0 := by decide
  omega

/-- **`θ_{3,3,3}` is not `2`-choosable**, witnessed by `ListColoring.thetaBadLists`: the first arm
has constant lists and blocks `(1,1)` and `(2,2)`, the other two block `(1,2)` and `(2,1)`. -/
theorem not_choosable_two_thetaGen_333 : ¬ (thetaGen 3 3 3).Choosable 2 := by
  intro h
  have hcard : ∀ v, (thetaBadLists 3 3 3 v).card = 2 := by decide
  have hpos := h (thetaBadLists 3 3 3) hcard
  have hzero : (thetaGen 3 3 3).col (thetaBadLists 3 3 3) = 0 := by decide
  omega

/-- **`θ_{2,4,4}` is not `2`-choosable**, witnessed by `ListColoring.thetaBadLists`: the arm of
length two blocks `(1,2)` and `(2,1)`, and the two arms of length four block `(1,1)` and `(2,2)`,
each routing through both auxiliary colors `3` and `4`. -/
theorem not_choosable_two_thetaGen_244 : ¬ (thetaGen 2 4 4).Choosable 2 := by
  intro h
  have hcard : ∀ v, (thetaBadLists 2 4 4 v).card = 2 := by decide
  have hpos := h (thetaBadLists 2 4 4) hcard
  have hzero : (thetaGen 2 4 4).col (thetaBadLists 2 4 4) = 0 := by decide
  omega

/-- `θ_{1,3,3}` is `2`-colorable: it is bipartite. -/
theorem colorable_two_thetaGen_133 : (thetaGen 1 3 3).Colorable 2 :=
  colConst_pos_iff_colorable.mp (by decide)

/-- `θ_{3,3,3}` is `2`-colorable: it is bipartite. -/
theorem colorable_two_thetaGen_333 : (thetaGen 3 3 3).Colorable 2 :=
  colConst_pos_iff_colorable.mp (by decide)

/-- **`θ_{3,3,3}` is `2`-colorable but not `2`-choosable**, hence not enumeratively
chromatic-choosable at `2`: it sits in the middle regime `χ(G) ≤ 2 < χ_ℓ(G)` of Kirov–Naimi. The
same holds for `θ_{1,3,3}`. -/
theorem not_ecc_two_thetaGen_333 : ¬ (thetaGen 3 3 3).ECCAt 2 :=
  not_ecc_of_colorable_of_not_choosable colorable_two_thetaGen_333
    not_choosable_two_thetaGen_333

/-- `θ_{1,3,3}` is `2`-colorable but not `2`-choosable, hence not enumeratively
chromatic-choosable at `2`. -/
theorem not_ecc_two_thetaGen_133 : ¬ (thetaGen 1 3 3).ECCAt 2 :=
  not_ecc_of_colorable_of_not_choosable colorable_two_thetaGen_133
    not_choosable_two_thetaGen_133

/-! ### Structural fragments

Two counting facts about the graphs that the hard direction has to deal with. They are the cheap
end of step 2: a connected graph of minimum degree `≥ 2` always has a cycle, and it has strictly
more edges than vertices — cyclomatic number `≥ 2`, the numerical shadow of "contains a theta" —
as soon as one vertex has degree `≥ 3`. -/

section Structural

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Minimum degree `≥ 2` forces at least three vertices. -/
theorem three_le_card_of_two_le_degree [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) :
    3 ≤ Fintype.card V := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h1 := hdeg v
  have h2 := G.degree_lt_card_verts v
  omega

/-- **A connected graph of minimum degree `≥ 2` contains a cycle.** A connected acyclic graph is a
tree, and a tree on at least two vertices has a vertex of degree one. -/
theorem exists_cycle_of_two_le_degree [Nonempty V] (hconn : G.Connected)
    (hdeg : ∀ v, 2 ≤ G.degree v) : ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  by_contra hcon
  push Not at hcon
  have hacyc : G.IsAcyclic := fun v c => hcon v c
  have htree : G.IsTree := ⟨hconn, hacyc⟩
  have hcard : 3 ≤ Fintype.card V := three_le_card_of_two_le_degree hdeg
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have h1 : G.minDegree = 1 := htree.minDegree_eq_one_of_nontrivial
  have h2 : 2 ≤ G.minDegree := G.le_minDegree_of_forall_le_degree 2 hdeg
  omega

/-- **A vertex of degree `≥ 3` forces more edges than vertices**, when every other vertex already
has degree `≥ 2`: the degree sum is at least `2 |V| + 1`. -/
theorem card_lt_card_edgeFinset (hdeg : ∀ v, 2 ≤ G.degree v) {u : V} (hu : 3 ≤ G.degree u) :
    Fintype.card V < G.edgeFinset.card := by
  have hsum : ∑ _v : V, 2 < ∑ v, G.degree v :=
    Finset.sum_lt_sum (fun v _ => hdeg v) ⟨u, Finset.mem_univ u, by omega⟩
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, G.sum_degrees_eq_twice_card_edges] at hsum
  omega

/-- The converse reading: a graph of minimum degree `≥ 2` with no more edges than vertices is
`2`-regular. Together with "a connected `2`-regular graph is a cycle" — the piece Mathlib does not
have — this is how a non-cycle produces the branch vertex that a theta subgraph is built from. -/
theorem degree_eq_two_of_card_edgeFinset_le (hdeg : ∀ v, 2 ≤ G.degree v)
    (h : G.edgeFinset.card ≤ Fintype.card V) (v : V) : G.degree v = 2 := by
  by_contra hv
  exact absurd (card_lt_card_edgeFinset hdeg (u := v) (by have := hdeg v; omega)) (by omega)

end Structural

/-! ### Theta shapes

### A removed definition, and why it must stay removed

An earlier version of this file carried a definition `ThetaAlternative H`, a four-way structural
disjunction:

> `H` is a cycle, or a `θ_{2,2,2m}`, or it contains an odd cycle, or it contains a theta
> `θ_{a,b,c}` of a shape other than `(2, 2, \text{even})`,

offered as the "purely structural" half of Rubin's hard direction. That definition was **invented in
this repository**; it is not Kirov–Naimi's, not Rubin's, and not from the literature at all. **It is
false** as a universal statement about connected graphs of minimum degree `≥ 2`, and it has been
deleted, together with everything that took it as a hypothesis. The refutation is by brute force on
a graph this development already owns: `SimpleGraph.ERT.K 2`, that is `K_{2,4}`.

* `K_{2,4}` is not a cycle and not any `θ_{2,2,2m}` — its degree sequence is `4, 4, 2, 2, 2, 2`,
  whereas a cycle is `2`-regular and a `θ_{2,2,2m}` has maximum degree three;
* it contains no odd cycle, being bipartite;
* it contains no *bad* three-arm theta: all six valid shapes with `a + b + c ≤ 7` fail to embed,
  and the only theta that does embed is the **good** `θ_{2,2,2}` — three internally disjoint paths
  between two of its vertices can only be three of the four length-two paths joining the two
  vertices of degree four.

Yet `K_{2,4}` is not `2`-choosable (`SimpleGraph.ERT.not_choosable 2`, the Erdős–Rubin–Taylor
example, in `ListColoring.NotChoosable`), so it is a counterexample to every disjunct at once.

The definition offered only *three-arm* thetas. The correct structural object is the **generalized
theta** — two vertices joined by arbitrarily many internally disjoint paths — and `K_{2,4}` is
precisely the generalized theta with four arms of length two. A universal structural statement
strong enough to finish Rubin's argument must therefore offer generalized thetas (and pairs of
cycles meeting in at most one vertex), each with its own non-choosability witness.

**This is a defect in this repository's scaffolding, and not an error in Kirov–Naimi**, whose proof
of Theorem 2 cites Rubin's theorem rather than proving it and therefore never asserts anything of
the kind. The distinction matters: no claim is being made here about the correctness of the paper.
The note is recorded so that the same shortcut is not reinvented; see also `provenance.md` §3.

What survives is `ListColoring.ThetaClassification`, discharged in `ListColoring.ThetaClass`, which
is a genuine theorem about theta graphs. -/

/-- A **valid, normalized** theta shape: `1 ≤ a ≤ b ≤ c` with `2 ≤ b`. Sorting the three arms
costs nothing, and `2 ≤ b` says at most one arm is a single edge — two would collapse to the same
edge and the "theta graph" would be a cycle. -/
def ValidShape (a b c : ℕ) : Prop := 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ 2 ≤ b

/-- **Rubin's shape**: `θ_{2,2,2m}`, in normalized form. -/
def GoodShape (a b c : ℕ) : Prop := a = 2 ∧ b = 2 ∧ Even c

/-- **The classification of `2`-choosable theta graphs**: a theta graph of any shape other than
`θ_{2,2,\text{even}}` fails to be `2`-choosable. This is Rubin's theorem restricted to the single
family of theta graphs — a far smaller loan than the classification of all `2`-choosable graphs,
and one whose every instance has an explicit finite witness.

What is proved above: the shapes `(1,3,3)`, `(3,3,3)` and `(2,4,4)` outright, on this very model;
`ListColoring.thetaBadLists` supplies the witness uniformly for every shape, and the `#guard` sweep
checks that it works for every valid shape with `a ≤ 4`, `b ≤ 4`, `c ≤ 5`. The whole family
`(2, 2, \text{odd})` is also proved outright, but on the model `ListColoring.thetaOf`, which is the
same graph with its vertices named differently — the two are matched numerically by the `colConst`
guards above, not by a formal isomorphism. What is missing is only the induction along an arm of
unbounded length that turns the uniform witness into a uniform proof. -/
def ThetaClassification : Prop :=
  ∀ a b c, ValidShape a b c → ¬ GoodShape a b c → ¬ (thetaGen a b c).Choosable 2

/-- **A worked, hypothesis-free instance**: a graph containing `θ_{3,3,3}` is not `2`-choosable.
The shape `(3,3,3)` is settled outright above, so nothing is borrowed here — this is the shape of
conclusion that the missing structural ingredient is supposed to feed. -/
theorem not_choosable_two_of_contains_theta333 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : Contains G (thetaGen 3 3 3)) :
    ¬ G.Choosable 2 :=
  not_choosable_of_contains not_choosable_two_thetaGen_333 h

end ListColoring

#print axioms ListColoring.not_choosable_of_contains
#print axioms ListColoring.not_choosable_two_of_contains_odd_cycle
#print axioms ListColoring.col_chain_const_odd
#print axioms ListColoring.colConst_thetaOf_odd
#print axioms ListColoring.not_choosable_two_thetaOf_odd
#print axioms ListColoring.not_choosable_two_thetaGen_133
#print axioms ListColoring.not_choosable_two_thetaGen_333
#print axioms ListColoring.not_choosable_two_thetaGen_244
#print axioms ListColoring.colorable_two_thetaGen_133
#print axioms ListColoring.colorable_two_thetaGen_333
#print axioms ListColoring.not_ecc_two_thetaGen_133
#print axioms ListColoring.not_ecc_two_thetaGen_333
#print axioms ListColoring.not_choosable_two_of_contains_theta333
#print axioms ListColoring.exists_cycle_of_two_le_degree
#print axioms ListColoring.three_le_card_of_two_le_degree
#print axioms ListColoring.card_lt_card_edgeFinset
#print axioms ListColoring.degree_eq_two_of_card_edgeFinset_le
