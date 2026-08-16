import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

#doc (Manual) "Which Graphs Are 2-Choosable?" =>

%%%
tag := "twochoosable"
%%%

Source:
[Choosable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Choosable.lean),
[ThetaChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ThetaChoosable.lean),
[Rubin.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Rubin.lean),
[ThetaGen.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ThetaGen.lean),
[ThetaClass.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ThetaClass.lean),
[TwoCycles.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/TwoCycles.lean),
[RubinStructure.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/RubinStructure.lean),
[RubinCases.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/RubinCases.lean),
[CoreExtract.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/CoreExtract.lean),
[RubinProof.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/RubinProof.lean).

The classification of the graphs that are enumeratively chromatic-choosable at `2`, which is the
second main theorem of the paper, rests on an older classification: which graphs are `2`-choosable?
That question was answered by A. L. Rubin, in the paper of Erdős, Rubin and Taylor
{citep erdosRubinTaylor}[] where list colouring is introduced, and the result is universally
credited to Rubin. Kirov and Naimi cite it. *This development proves it*, and as far as we can
determine that is the first time a machine has checked it.

The short version: {name ListColoring.rubinTheorem}`rubinTheorem` is a theorem, with no hypotheses
and no `sorry`, so {ref "twoecc"}[Theorem 2 of Kirov–Naimi] is unconditional. Nothing in this
chapter is new mathematics; the argument below is Rubin's own, from 1979, spelled out in the detail
a machine wants.

# Pendant vertices do not matter

Start with the reduction that makes a classification possible at all. A vertex of degree one can
always be coloured last: whatever colour its single neighbour took, its own list of two colours
still contains something else. So attaching a pendant vertex changes nothing about `2`-choosability
— nor about `n`-choosability for any `n ≥ 2`:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
    (hn : 2 ≤ n) (k : ℕ) (d : TowerData V k) :
    (pendantTower G k d).Choosable n ↔ G.Choosable n :=
  choosable_pendantTower_iff hn k d
```

Repeatedly deleting vertices of degree one until none is left produces the *core* of the graph. The
statement above is that reduction run backwards, which is the form a formalization can use directly:
rather than define a fixpoint of a deletion operation, present the graph as its core with a tower of
pendant attachments on top. That reading is what {name SimpleGraph.CoreIs}`CoreIs` says, and it is
spelled out exactly so:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    CoreIs G H ↔
      ∃ (k : ℕ) (d : TowerData W k),
        Nonempty (G ≃g pendantTower H k d) :=
  Iff.rfl
```

This is mechanization and not mathematics — the papers simply say "core" — and the two readings are
interchangeable because of the display above it. Choosability transports along it:

```lean
open SimpleGraph ListColoring in
example {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (h : CoreIs G H) : G.Choosable 2 ↔ H.Choosable 2 :=
  choosable_iff_of_coreIs h le_rfl
```

So the classification only has to describe the possible cores, and those have minimum degree at
least two.

# Rubin's list

*A connected graph is `2`-choosable if and only if its core is a single vertex, an even cycle, or
$`\theta_{2,2,2m}` for some $`m \ge 1`.*

```diagram (cssWidth := "96%")
open Illuminate Diagram in
let v (x y : Float) : Diagram SVG := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram SVG := line ⟨x1, y1⟩ ⟨x2, y2⟩
-- a single vertex
let one := [v (-400) 0, translate (-400) (-46) (text "a single vertex")]
-- an even cycle, drawn as a hexagon
let hex :=
  [e (-80) 0 (-115) 61, e (-115) 61 (-185) 61, e (-185) 61 (-220) 0,
   e (-220) 0 (-185) (-61), e (-185) (-61) (-115) (-61), e (-115) (-61) (-80) 0,
   v (-80) 0, v (-115) 61, v (-185) 61, v (-220) 0, v (-185) (-61), v (-115) (-61),
   translate (-150) (-100) (text "an even cycle")]
-- the theta graph
let th :=
  [e 140 0 205 0, e 205 0 270 0, e 270 0 335 0, e 335 0 400 0,
   e 140 0 270 70, e 270 70 400 0, e 140 0 270 (-70), e 270 (-70) 400 0,
   v 140 0, v 205 0, v 270 0, v 335 0, v 400 0, v 270 70, v 270 (-70),
   translate 270 22 (text "length 2m"),
   translate 270 (-100) (text "theta(2,2,2m)")]
(one ++ hex ++ th).foldl atop emptyDiagram
```

That sentence is a theorem:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.Choosable 2 ↔
      CoreIsVertex G ∨ CoreIsEvenCycle G ∨ CoreIsTheta G :=
  rubinTheorem G hconn
```

It is also a *named proposition*, so that statements which consume it can be written against it
independently of when it lands — which is how {ref "twoecc"}[Theorem 2] was stated while this
chapter's proof was still being built. Unfolded, the name reads:

```lean
open ListColoring in
example : RubinTheorem =
    ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → (G.Choosable 2 ↔
        CoreIsVertex G ∨ CoreIsEvenCycle G ∨
          CoreIsTheta G) :=
  rfl
```

```lean
open ListColoring in
example : RubinTheorem := rubinTheorem
```

The three alternatives are the three families, each said of the *core* by way of the definition
above. Recall that `closePath k` has `k + 1` vertices, so `Odd k` picks out the cycles on an *even*
number of vertices:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ListColoring.CoreIsEvenCycle G ↔
      ∃ k, Odd k ∧ 2 ≤ k ∧ CoreIs G (closePath k) := Iff.rfl
```

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ListColoring.CoreIsTheta G ↔ ∃ m, 1 ≤ m ∧ CoreIs G (theta m) :=
  Iff.rfl
```

The same three families collected up to isomorphism, without the core, are
{name ListColoring.RubinFamily}`RubinFamily`:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    RubinFamily G ↔ (Subsingleton V ∨
      (∃ k, Odd k ∧ 2 ≤ k ∧ Nonempty (G ≃g closePath k)) ∨
      (∃ m, 1 ≤ m ∧ Nonempty (G ≃g theta m))) :=
  Iff.rfl
```

The smallest theta on the list, $`\theta_{2,2,2}`, is $`K_{2,3}` — two branch vertices joined by
three paths of length two is exactly two vertices each joined to the same three others.

# The easy direction, proved

Everything on Rubin's list really is `2`-choosable:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : RubinFamily G) : G.Choosable 2 :=
  choosable_two_of_rubinFamily G h
```

and therefore, transported along the core, in the form in which Rubin's theorem states it:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : CoreIsVertex G ∨ CoreIsEvenCycle G ∨
      CoreIsTheta G) : G.Choosable 2 :=
  choosable_two_of_rubinAlternatives h
```

That display is worth pausing on: it is one half of {name ListColoring.RubinTheorem}`RubinTheorem`,
discharged. What is missing from the named proposition is only its *forward* implication.

The three cases are of quite different weights.

*A single vertex* is `n`-choosable for any `n ≥ 1`, there being no edge to violate.

*An even cycle* is a corollary of Theorem 1 rather than a separate argument, and this is the
pleasing part. Enumerative chromatic-choosability at `2` says the uniform assignment minimizes the
count; for an even cycle that minimum is $`\mathrm{col}(C, 2) = 2`; so *every* `2`-list assignment
on an even cycle admits at least two colourings, in particular at least one.

```lean
open ListColoring in
example {k : ℕ} (hk : Odd k) (hk2 : 2 ≤ k) :
    (closePath k).Choosable 2 :=
  choosable_two_closePath_of_odd hk hk2
```

The odd cycles are excluded for the bluntest possible reason — they are not even `2`-colourable:

```lean
open ListColoring in
example {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    ¬ (closePath k).Choosable 2 :=
  not_choosable_two_closePath_of_even hk hk2
```

*The theta graphs* need a genuine argument. Colour the two branch vertices first; a pair of colours
for them either agrees or differs, and one checks that each arm can be completed in at least one of
the cases. The two length-two arms handle the pairs the long arm cannot.

```lean
open ListColoring in
example (m : ℕ) (hm : 1 ≤ m) : (theta m).Choosable 2 :=
  choosable_theta m hm
```

# The forward direction

The other half — that a `2`-choosable graph's core *must* be on the list — is the long one. It has
a colouring part, which supplies the obstructions, and a structural part, which finds one of them
inside any graph that is not on the list. Both are proved. The colouring part comes first.

## The theta graphs are classified

A general theta graph $`\theta_{a,b,c}` is two branch vertices joined by three internally disjoint
paths of lengths `a`, `b`, `c`. Normalize the shape so that $`1 \le a \le b \le c` with $`b \ge 2` —
sorting costs nothing, and $`b \ge 2` says at most one arm is a bare edge, since two would collapse:

```lean
open ListColoring in
example {a b c : ℕ} :
    ValidShape a b c ↔
      1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ 2 ≤ b := Iff.rfl
```

```lean
open ListColoring in
example {a b c : ℕ} :
    GoodShape a b c ↔ a = 2 ∧ b = 2 ∧ Even c := Iff.rfl
```

Rubin's list contains exactly the good shapes, and for theta graphs that is now a theorem in both
directions:

```lean
open ListColoring in
example {a b c : ℕ} (hv : ValidShape a b c) :
    (thetaGen a b c).Choosable 2 ↔ GoodShape a b c :=
  choosable_two_thetaGen_iff hv
```

The ⟸ half of that is Rubin's family again, on the general model:

```lean
open ListColoring in
example (m : ℕ) (hm : 1 ≤ m) :
    (thetaGen 2 2 (2 * m)).Choosable 2 :=
  choosable_two_thetaGen_two_two m hm
```

The ⟹ half is an explicit `2`-list assignment admitting no colouring, uniform in the shape:

```lean
open ListColoring in
example {a b c : ℕ} (hv : ValidShape a b c)
    (hbad : ¬ GoodShape a b c) :
    ¬ (thetaGen a b c).Choosable 2 :=
  not_choosable_two_thetaGen hv hbad
```

```lean
open ListColoring in
example : ThetaClassification := thetaClassification
```

The witness gives both branch vertices the list `{1, 2}`, so a colouring is a pair of branch colours
plus a completion along each arm; an arm *blocks* a pair when no completion exists. An arm whose
interior lists are all `{1,2}` forces the two ends to alternate, so it blocks two pairs according to
its parity; an arm carrying a suitably staggered pattern of lists propagates a forced chain and
blocks a single pair. Either $`b = 2` — and then the shape contains an odd cycle and the uniform
lists already fail — or $`3 \le b \le c` and the three arms between them block all four pairs. Small
shapes are also checked outright:

```lean
open ListColoring in
example : ¬ (thetaGen 3 3 3).Choosable 2 :=
  not_choosable_two_thetaGen_333
```

```lean
open ListColoring in
example : ¬ (thetaGen 2 4 4).Choosable 2 :=
  not_choosable_two_thetaGen_244
```

## Beyond three arms

Three arms are not enough, for a reason the last section of this chapter tells at length. The
*generalized* theta $`\Theta(k_1,\dots,k_n)` joins its two branch vertices by `n`
internally disjoint paths, `n` arbitrary, and the classification holds at every arity — with the
same normalization, sorted arms, at most one of length one:

```lean
open ListColoring in
example {ks : List ℕ} :
    ValidArms ks ↔
      3 ≤ ks.length ∧ ks.Pairwise (· ≤ ·) ∧
      (∀ i, ∀ hi : i < ks.length, 1 ≤ ks[i]) ∧
      (∀ i, ∀ hi : i < ks.length, 1 ≤ i → 2 ≤ ks[i]) :=
  Iff.rfl
```

```lean
open ListColoring in
example {ks : List ℕ} :
    GoodArms ks ↔ ∃ m, 1 ≤ m ∧ ks = [2, 2, 2 * m] := Iff.rfl
```

```lean
open ListColoring in
example {ks : List ℕ} (hv : ValidArms ks) :
    (gtheta ks).Choosable 2 ↔ GoodArms ks :=
  choosable_two_gtheta_iff hv
```

Read the arity off the right-hand side: `GoodArms` forces a list of length three, so *no*
generalized theta on four or more arms is `2`-choosable, whatever its arm lengths. That half is
proved directly, because it is what the structural argument consumes:

```lean
open ListColoring in
example {ks : List ℕ} (hn : 4 ≤ ks.length)
    (h1 : 1 ≤ ks[0]'(by omega))
    (h2 : ∀ i, ∀ hi : i < ks.length, 1 ≤ i → 2 ≤ ks[i]) :
    ¬ (gtheta ks).Choosable 2 :=
  not_choosable_two_gtheta_of_four hn h1 h2
```

The witness is the Erdős–Rubin–Taylor transversal construction with the colours renamed: branch
lists $`\{1,2\}` and $`\{3,4\}`, and four arms carrying $`\{1,3\}`, $`\{1,4\}`, $`\{2,3\}`,
$`\{2,4\}` — one arm to block each of the four pairs of branch colours. Note this is proved *from
list assignments*, not from Rubin's theorem, which is what stops the argument being circular: the
classification feeds the proof of Rubin's theorem rather than following from it.

## The obstructions, in full

Five configurations are not `2`-choosable, and between them they are everything Rubin's argument
needs. All five are proved.

*An odd cycle*, for the bluntest reason: it is not `2`-colourable, and a graph containing it
inherits that.

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : Even k) (hk2 : 2 ≤ k)
    (h : Contains G (closePath k)) : ¬ G.Choosable 2 :=
  not_choosable_two_of_contains_odd_cycle hk hk2 h
```

*A dumbbell* — two cycles joined by a path, meeting nothing else — and, as the degenerate case of
the same statement, *a figure-eight*, two cycles sharing a single vertex. In a connected graph the
two collapse into one clean statement:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v z : V}
    {c₁ : G.Walk v v} {c₂ : G.Walk z z}
    (hconn : G.Connected)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (hmeet : ∀ x y : V, x ∈ c₁.support → y ∈ c₁.support →
      x ∈ c₂.support → y ∈ c₂.support → x = y) :
    ¬ G.Choosable 2 :=
  not_choosable_two_of_cycles_meet_le_one hconn hc₁ hc₂ hmeet
```

That connectivity hypothesis is doing real work and is not decoration: *two disjoint even cycles are
`2`-choosable*, since colourings of a disjoint union are independent and each even cycle has one.
What a cut vertex in a connected graph of minimum degree two actually hands you is a dumbbell, with
the connecting path allowed to be trivial. Underneath sits the raw indexed form, which is what the
colour-forcing chain is written against:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (A B : ℕ → V)
    (hA : ∀ i, i < m → G.Adj (A i) (A (i + 1)))
    (hAcl : G.Adj (A m) (A 0))
    (hB : ∀ k, k < n → G.Adj (B k) (B (k + 1)))
    (hBcl : G.Adj (B n) (B 0))
    (hAB0 : A 0 = B 0)
    (hAinj : Set.InjOn A (Set.Iic m))
    (hBinj : Set.InjOn B (Set.Iic n))
    (hdisj : ∀ i, i ≤ m → ∀ k, 1 ≤ k → k ≤ n → A i ≠ B k) :
    ¬ G.Choosable 2 :=
  not_choosable_two_of_figureEight hm hn A B hA hAcl hB hBcl
    hAB0 hAinj hBinj hdisj
```

The forcing argument behind it is worth a sentence, because it is shorter than the one usually
given. Along a walk, give the `(i+1)`-st vertex the list $`\{c_i, c_{i+1}\}` with consecutive
colours distinct; then fixing the first vertex to $`c_0` forces every later one, since a vertex may
not repeat its predecessor's colour and has only one alternative. Closing the walk into a cycle with
$`c_m = c_0` gives a contradiction, so *one prescribed colour is killed at the base point of a
cycle, whatever the cycle's parity*. The informal argument splits on parity here; it does not need
to.

*A bad three-arm theta*, and *a generalized theta on four or more arms* — the two halves of the
classification above.

## Rubin's argument, and what it does not need

The received account of this theorem routes the structural step through a block or ear
decomposition. Mathlib has neither, and building one is a substantial piece of graph theory
unrelated to colouring. An earlier plan for this development took that route, invented an auxiliary
structural hypothesis to stand in for it, and — twice — found the hypothesis was false.

Rubin's own argument needs *none of it*: no ear decomposition, no Menger, not even
`2`-connectivity. It runs on a shortest cycle, two shortest connecting paths, and a case analysis.
Here is the whole of it.

*Pass to the core.* Deleting vertices of degree one until none is left is a classical move that
papers state in a clause; a formalization has to produce it. The result is connected, and is either
a single vertex or has minimum degree at least two:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasCore G ↔
      ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
        (H : SimpleGraph W) (_ : DecidableRel H.Adj),
        H.Connected ∧
        (Fintype.card W = 1 ∨ ∀ w : W, 2 ≤ H.degree w) ∧
        CoreIs G H :=
  Iff.rfl
```

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) : HasCore G :=
  hasCore G hG
```

*Take a shortest cycle* $`C_1`. It exists because the minimum degree is at least two — the proof is
a count rather than the usual longest-path argument: a connected acyclic graph has `n - 1` edges
while minimum degree two forces at least `n`. Shortest, because minimality is used twice later:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      ∀ (w : V) (d : G.Walk w w), d.IsCycle →
        c.length ≤ d.length :=
  exists_shortest_isCycle hconn hdeg
```

*Take a shortest connecting path* $`P_1`: edge-disjoint from $`C_1`, joining two distinct vertices
of it, and meeting it nowhere in between. Rubin writes "(This is now known to exist.)"; the
parenthesis is the whole of the work. Existence is where `2`-choosability enters the structural
half, and it enters through the dumbbell: extend an edge leaving $`C_1` to a *longest* path whose
interior avoids $`C_1`, and either its far end has a second neighbour on $`C_1` — that is the
connecting path — or a cycle closes inside the path, meeting $`C_1` in at most one vertex, which
the previous section has already excluded.

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (hch : G.Choosable 2) {v : V} {c : G.Walk v v}
    (hc : c.IsCycle)
    (hedge : ∃ x y : V, G.Adj x y ∧ s(x, y) ∉ c.edges) :
    ∃ (a b : V) (p : G.Walk a b),
      a ∈ c.support ∧ b ∈ c.support ∧ a ≠ b ∧
      p.IsPath ∧ 1 ≤ p.length ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support) ∧
      ∀ e ∈ p.edges, e ∉ c.edges :=
  exists_connecting_path_of_cycle_of_choosable hconn hdeg hch hc hedge
```

That statement is proved in more generality than a cycle: for an arbitrary vertex set `S` and an
arbitrary set of already-used edges, because Rubin's step 5 applies the very same reasoning with
$`C_1` replaced by $`C_1 \cup P_1`.

*Steps 4 and 5.* $`C_1 \cup P_1` is a theta, and its shape is forced. If $`P_1` were odd, or if an
arc of $`C_1` had length other than two, some arm arrangement would be a bad theta — and a bad theta
is not `2`-choosable. So $`C_1` is a four-cycle and $`P_1` has even length at least two, which is to
say $`C_1 \cup P_1` is exactly $`\theta_{2,2,2m}` with the ends of $`P_1` as branch vertices. That
is {name ListColoring.step4}`step4`.

*Step 6.* No further edge exists. Apply the connecting-path lemma again, now with $`S = C_1 \cup
P_1`, to get a second path $`P_2`, and go through the cases on where its two ends sit — both on
$`P_1`, both in the interior of an arc, one of each, both at branch vertices, both at the middle
vertices `u` and `w` of the four-cycle. Each case exhibits one of the five obstructions. That is
{name ListColoring.step56}`step56`, and the two together are the structural half:

```lean
open ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ z : V, 2 ≤ G.degree z)
    (hch : G.Choosable 2) :
    (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Even c.length ∧
        (∀ z : V, z ∈ c.support) ∧
        ∀ x y : V, G.Adj x y → s(x, y) ∈ c.edges) ∨
    (∃ (v : V) (c : G.Walk v v) (a b u w : V) (p : G.Walk a b),
      c.IsCycle ∧ c.length = 4 ∧
      a ∈ c.support ∧ b ∈ c.support ∧ a ≠ b ∧ u ≠ w ∧
      G.Adj a u ∧ G.Adj u b ∧ G.Adj a w ∧ G.Adj w b ∧
      (∀ z, z ∈ c.support → z = a ∨ z = u ∨ z = b ∨ z = w) ∧
      p.IsPath ∧ Even p.length ∧ 2 ≤ p.length ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∉ c.support) ∧
      (∀ e ∈ p.edges, e ∉ c.edges) ∧
      (∀ z : V, z ∈ c.support ∨ z ∈ p.support) ∧
      ∀ x y : V, G.Adj x y →
        s(x, y) ∈ c.edges ∨ s(x, y) ∈ p.edges) :=
  rubin_structure hconn hdeg hch
```

The conclusion is *data about walks*, not an isomorphism, and deliberately so: the two branches are
consumed by two different recognition lemmas, and keeping them apart is what lets each be proved
once.

*Recognize the answer.* A connected `2`-regular graph is a cycle; a graph that is exactly three
internally disjoint paths between two vertices is a theta graph. Neither Rubin nor Kirov–Naimi
proves these — a paper says them in a clause — and both have to be built:

```lean
open ListColoring in
example {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (hconn : H.Connected) (hdeg : ∀ w : W, H.degree w = 2) :
    ∃ k, 2 ≤ k ∧ Nonempty (H ≃g closePath k) :=
  exists_iso_closePath_of_two_regular hconn hdeg
```

And that is the theorem. The first branch of the structure theorem gives a `2`-regular core, hence a
cycle, necessarily even because odd cycles are not `2`-choosable; the second gives
$`\theta_{2,2,2m}`; the core case of a single vertex is the remaining alternative.

# Three corrections to the published argument

Rubin's exposition dates from 1979 and is three pages long. Three points in it do not survive
mechanization as printed. All three were found the same way — by running his procedure exhaustively
over all `316,460` connected bipartite non-cycle graphs of minimum degree at least two on at most
eight vertices, trying *every* shortest cycle, every shortest admissible $`P_1` and every shortest
admissible $`P_2` — and all three are recorded in the development, in the module docstrings of
{name ListColoring.rubin_structure}`RubinCases` and its imports.

*Cases (i) and (ii) of the six cannot occur.* Both describe a $`P_2` producing a cycle that meets
$`C_1` in at most one node — none at all in case (i), exactly one in case (ii) — and step 3 has
already disposed of every graph that has such a cycle. Rubin notices this in passing ("we are in
case (2.) again"), but a formalization does not have to treat them as cases at all: they contradict
a hypothesis the connecting-path lemma is already carrying. Neither fires anywhere in the sweep.

*Case (v) silently relies on $`P_1` being shortest.* With $`P_2` joining the two branch vertices the
four arms have lengths `2`, `2`, $`|P_1|`, $`|P_2|`, and Rubin's "if $`P_1` is of length `> 2` then
we are in case (4.)" is correct only because $`P_2` is itself an admissible path for $`C_1`, so
$`|P_1| \le |P_2|`. Take $`P_1` non-minimal and the claim fails outright: arms `2, 2, 4, 2` contain
no bad three-arm theta. The formalization drops the sub-split instead and uses four arms of any
lengths — which is exactly the arity-four case above, and is why that case had to be proved.

*Step 5's "$`C_1` is a four-cycle" needs minimality of $`C_1`.* If the theta $`C_1 \cup P_1` has
shape `2, 2, ℓ` with the two `2`s the arcs of $`C_1`, that is immediate; but if instead an arc and
$`P_1` are the two `2`s, one has to observe that the four-cycle they form is at least as short as
$`C_1`. The hypothesis enters {name ListColoring.step4}`step4` as `hmin`.

None of this is a criticism of Kirov and Naimi, who cite Rubin's theorem rather than proving it.
They are gaps in a forty-year-old three-page exposition of the kind that only a machine, or a very
patient reader, would notice — and each is a gap in the *writing*, not in the result: the theorem is
true, and is now checked.

# The counterexamples: $`K_{2,4}` and $`K_{3,3} - e`

An earlier version of this development carried an auxiliary hypothesis, invented here and not found
in any paper, meant to be the structural half of the argument. Applied to a graph `H`, it offered
four alternatives:

> `H` is a cycle, or a $`\theta_{2,2,2m}`, or it contains an odd cycle, or it contains a theta
> $`\theta_{a,b,c}` of some shape other than $`(2,2,\text{even})`.

Every disjunct is a configuration whose colouring behaviour is settled above, so the hypothesis
looked like exactly the right currency. *It is false*, and it has been deleted along with
everything that took it as a hypothesis. The counterexample is a graph this book has already met:
$`K_{2,4}`, the Erdős–Rubin–Taylor example of {ref "lists"}[the lists chapter], which lives here as
`ERT.K 2` — the complete bipartite graph whose right side is indexed by the four functions
$`\mathbf{2} \to \mathbf{2}`.

```lean
open SimpleGraph in
example : ERT.K 2 =
    completeBipartiteGraph (Fin 2) (Fin 2 → Fin 2) := rfl
```

```lean
open SimpleGraph in
example : Fintype.card (Fin 2 → Fin 2) = 2 ^ 2 :=
  ERT.card_right 2
```

```diagram (cssWidth := "80%")
open Illuminate Diagram in
let v (x y : Float) : Diagram SVG := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram SVG := line ⟨x1, y1⟩ ⟨x2, y2⟩
let left := [v (-160) 0, v 160 0]
let mid := [v 0 120, v 0 40, v 0 (-40), v 0 (-120)]
let edges :=
  [e (-160) 0 0 120, e (-160) 0 0 40, e (-160) 0 0 (-40), e (-160) 0 0 (-120),
   e 160 0 0 120, e 160 0 0 40, e 160 0 0 (-40), e 160 0 0 (-120)]
let labels :=
  [translate (-160) (-30) (text "degree 4"), translate 160 (-30) (text "degree 4"),
   translate 0 (-166) (text "K(2,4): four arms of length two")]
(edges ++ left ++ mid ++ labels).foldl atop emptyDiagram
```

Check $`K_{2,4}` against the four alternatives. It is connected, and its minimum degree is two.

*Not a cycle, and not any* $`\theta_{2,2,2m}`. Its degree sequence is `4, 4, 2, 2, 2, 2`, whereas a
cycle is `2`-regular and a $`\theta_{2,2,2m}` has maximum degree three.

```lean
open SimpleGraph in
example : (ERT.K 2).degree (Sum.inl 0) = 4 := by decide
```

```lean
open SimpleGraph in
example : ∀ φ : Fin 2 → Fin 2,
    (ERT.K 2).degree (Sum.inr φ) = 2 := by decide
```

*No odd cycle.* It is bipartite, hence `2`-colourable, and a graph with an odd cycle is not:

```lean
open SimpleGraph in
example : ¬ ListColoring.HasOddCycle (ERT.K 2) := fun h =>
  ListColoring.not_colorable_two_of_hasOddCycle h
    (ERT.colorable 2 le_rfl)
```

*No bad theta.* A theta subgraph has two branch vertices of degree at least three *in the subgraph*,
so of degree at least three in $`K_{2,4}` — which leaves only the two vertices of degree four. Those
two are not adjacent, and the only paths between them that are internally disjoint are the four
length-two paths through the right-hand vertices. So every theta subgraph of $`K_{2,4}` consists of
three of those four paths: it is a $`\theta_{2,2,2}`, and that is the *good* shape.

```lean
open SimpleGraph ListColoring in
example : Contains (ERT.K 2) (thetaGen 2 2 2) :=
  ⟨![Sum.inr ![0, 0], Sum.inr ![0, 1], Sum.inr ![1, 1],
     Sum.inl 0, Sum.inl 1], by decide, by decide⟩
```

```lean
open ListColoring in
example : (thetaGen 2 2 2).Choosable 2 :=
  choosable_two_thetaGen_two_two 1 le_rfl
```

So all four alternatives fail. And yet:

```lean
open SimpleGraph in
example : ¬ (ERT.K 2).Choosable 2 := ERT.not_choosable 2
```

```lean
open SimpleGraph in
example : (ERT.K 2).Colorable 2 := ERT.colorable 2 le_rfl
```

Six vertices and eight edges is enough to refute the hypothesis outright.

## What the first counterexample taught

Look at the picture again. $`K_{2,4}` *is* a theta graph — it is two vertices joined by internally
disjoint paths, all of length two. What it is not is a theta graph with *three* arms. The discarded
hypothesis offered only three-arm thetas, and that is precisely where it was too weak.

The right object is the *generalized theta*: two vertices joined by arbitrarily many internally
disjoint paths. $`K_{2,4}` is the one with four arms of length two, and it is the smallest graph
that a three-arm dichotomy cannot see. That is the classification proved above, and it holds at
every arity — including the fact that $`K_{2,4}` itself is not `2`-choosable, obtained from the
arity-four case by a route independent of the original Erdős–Rubin–Taylor witness:

```lean
open SimpleGraph ListColoring in
example : ¬ (ERT.K 2).Choosable 2 := not_choosable_two_K24
```

The two proofs agree, as they must; the second is the transversal construction with the colours
renamed.

## The second counterexample: $`K_{3,3} - e`

The natural repair of the refuted hypothesis was to replace three-arm thetas by generalized ones:

> `H` is a cycle, or it *is* a generalized theta, or it contains two cycles meeting in at most one
> vertex.

*That is false too*, and the counterexample again has six vertices: $`K_{3,3}` minus an edge. Four
of its vertices have degree at least three, whereas a generalized theta has exactly two; and its
girth is four, so two cycles meeting in at most one vertex would need seven vertices between them.
An exhaustive sweep of the `129,073` bipartite `2`-connected non-cycle graphs on at most nine
vertices finds `4,162` satisfying neither branch.

Note the *is*. Under a *contains* reading $`K_{3,3} - e` refutes nothing at all, since it contains
both $`\theta_{1,3,3}` and $`\theta_{2,2,2}` — which is precisely why containment is the wrong
predicate here. A good theta is `2`-choosable, so exhibiting a theta subgraph implies nothing; what
matters is containing a *bad* one. The shape of the mistake repeated itself twice: *contains* and
*is* are not interchangeable, and neither are "a theta" and "a bad theta".

A third alternative, adding a dumbbell branch, does close all `129,073` cases — but only
empirically. It was never proved, and in the end it was not needed: Rubin's own steps 4 to 6 replace
the whole structural detour, which is why the argument in this chapter never mentions a dichotomy at
all.

## What the episode is worth

Three things, stated plainly because they are easy to garble.

First, *these were defects in this repository's scaffolding, not errors in Kirov–Naimi*. The
hypotheses were invented here, as a way of splitting Rubin's theorem into a structural half and a
colouring half so that the halves could be worked on separately. Kirov and Naimi *cite* Rubin's
theorem rather than proving it, and so never assert anything of the kind. No error has been found in
their paper — zero, across the whole formalization. Every refuted claim in this project has been one
of ours.

Second, the false starts left something behind. The classification of generalized thetas at
arbitrary arity was forced by $`K_{2,4}` and is now what discharges Rubin's type 5; the dumbbell was
forced by $`K_{3,3} - e` and is now what discharges his step 3. Both are load-bearing in the final
proof. The scaffolding was wrong; the lemmas it demanded were not.

Third, the episode is an argument for the discipline this book runs on rather than against it. Each
hypothesis was plausible, was consistent with every example anyone had checked by hand, and was
refuted by brute force on a six-vertex graph. That is the ordinary working of mechanization: a
statement that will not close is a statement worth attacking with a search.

# What this buys

With Rubin's theorem proved, {ref "twoecc"}[the next chapter] can ask which of the `2`-choosable
graphs are actually enumeratively chromatic-choosable at `2`, and get an answer that assumes
nothing. There are not many candidates to sort through: a single vertex, the even cycles, and the
theta graphs. All three families are settled by theorems already proved.
