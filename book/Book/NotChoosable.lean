import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Colorable but Not Choosable" =>

%%%
tag := "notchoosable"
%%%

Source:
[NotChoosable.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/NotChoosable.lean).

Section 5 of the paper constructs, for each `n`, a graph that is `n`-choosable but *not*
enumeratively chromatic-choosable at `n` — showing that the two notions, which the characterization
of graphs that are enumeratively chromatic-choosable at `2` makes look almost identical, genuinely
come apart. The construction is assembled from many copies of one building block: a complete
bipartite graph that is `n`-colorable but not `n`-choosable. This chapter builds that block first,
and then the graph itself.

# The separating assignment

Take the complete bipartite graph with `n` vertices on one side and `nⁿ` on the other. The trick is
to index the large side by *functions* `Fin n → Fin n`, so that "there are `nⁿ` of them" is a fact
about the type rather than an arithmetic side condition:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : Fintype.card (Fin n → Fin n) = n ^ n :=
  card_right n
```

Now assign lists as follows. The `i`-th vertex on the small side gets the `i`-th block of `n`
consecutive colours, so the small side's lists are pairwise disjoint. The vertex indexed by `φ` on
the large side gets one colour from each block, namely the one `φ` selects. Every list has exactly
`n` colours:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : IsNListAssignment (L₀ n) n :=
  isNListAssignment_L₀ n
```

And there are no colorings at all:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : (K n).col (L₀ n) = 0 :=
  col_L₀_eq_zero n
```

The argument is short and does not need induction. A proper coloring must choose, at each small-side
vertex `i`, some colour from the `i`-th block — that is, it determines a function `φ`. Now look at
the *single* large-side vertex indexed by that very `φ`. Its list is exactly the set of colours the
coloring has just used on the small side, and it is adjacent to all of them. So it has nothing left,
and no such coloring exists. The large side is precisely large enough to enumerate every possible
choice and block each one.

# The separation

Consequently the graph is not `n`-choosable:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) : ¬ (K n).Choosable n :=
  not_choosable n
```

but it is `n`-colorable, being bipartite:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) (hn : 2 ≤ n) : (K n).Colorable n :=
  colorable n hn
```

So it sits squarely in the regime identified in the first chapter — colorable but not choosable —
and is therefore not enumeratively chromatic-choosable:

```lean
open SimpleGraph SimpleGraph.ERT in
example (n : ℕ) (hn : 2 ≤ n) : ¬ (K n).ECCAt n :=
  not_ecc n hn
```

The smallest instance, `K 2`, is $`K_{2,4}`, and it earns its keep twice over: besides being the
building block here it is the counterexample that killed this development's first attempt at the
structural half of Rubin's theorem, and so forced the classification of generalized theta graphs at
arbitrary arity that the real proof runs on. {ref "twochoosable"}[The `2`-choosability chapter]
tells that story, and reproves this very statement from the arity-four case — a second, independent
route to the same fact.

This last line is a one-liner from the three-regime observation, but it is worth pausing on: it is a
complete, if easy, instance of the paper's theme. What Section 5 goes on to do is much harder —
build a graph that *is* `n`-choosable and still fails to be enumeratively chromatic-choosable at
`n`, so that the failure cannot be explained away by non-choosability.

# The graph itself

Take `n` vertices $`v_1, \dots, v_n` and `p` vertices $`w_1, \dots, w_p` forming a complete
bipartite graph, together with $`n^2` disjoint copies $`G_{i,j}` of the block above, and join each
$`v_i` to *every* vertex of the `n` copies $`G_{i,1}, \dots, G_{i,n}`. That is the paper's
$`H_{n+1}`, and `p` is left free for a counting argument to fix later:

```lean
open SimpleGraph in
example (n p : ℕ) : SimpleGraph (KN5.HV n p) := KN5.H n p
```

The lists do the rest. Rename the block's separating assignment $`L_0` so its colours are out of the
way, then add one extra colour `j` to every list of the copy $`G_{i,j}`. The copy still cannot be
coloured without using `j` somewhere — that is what the renamed $`L_0` being uncolourable means — and
$`v_i` sees all of it. So the colour of every $`v_i` is forced, and then the colour of every $`w_k`
is forced too, and the number of colourings collapses to a quantity independent of `p`. Meanwhile
the *constant* list of size `n+1` admits at least $`n^p` colourings, because the $`w_k` may be
coloured freely. Choose `p` large and the constant assignment is no longer the minimizer. That is
Lemma 7:

```lean
open SimpleGraph Finset in
example {n p : ℕ} (hn : 2 ≤ n)
    (hp : (∏ j : Fin n, (ERT.K n).col (KN5.Lblock n j.val)) ^ n < n ^ p) :
    ¬ (KN5.H n p).ECCAt (n + 1) :=
  KN5.not_ecc hn hp
```

and such a `p` always exists, since $`m < n^m` once `n ≥ 2`:

```lean
open SimpleGraph Finset in
example {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, (∏ j : Fin n, (ERT.K n).col (KN5.Lblock n j.val)) ^ n < n ^ p :=
  KN5.exists_pow_lt hn
```

The choosability half is the delicate one. For each $`v_i` we must find a colour that none of the
`n` copies below it objects to, and the copies are where the difficulty lives: deleting a colour
from every list of a $`K_{n,n^n}` can destroy every colouring. Lemma 9 is the bound that makes it
work — at most *one* colour can do that:

```lean
open SimpleGraph in
example {n : ℕ} (hn : 2 ≤ n) {M : ListAssignment (KN5.BV n)}
    (hM : ∀ u, n + 1 ≤ (M u).card) {c c' : ℕ}
    (hc : (ERT.K n).col (fun u => (M u).erase c) = 0)
    (hc' : (ERT.K n).col (fun u => (M u).erase c') = 0) : c = c' :=
  KN5.badColor_unique hn hM hc hc'
```

so the `n` copies rule out at most `n` of the `n+1` colours in $`L(v_i)`, leaving one. Each $`w_k`
has only the `n` neighbours $`v_1, \dots, v_n`, so its list has a spare colour too. That is
Lemma 10, and the two halves together are Section 5's theorem:

```lean
open SimpleGraph in
example {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, (KN5.H n p).Choosable (n + 1) ∧ ¬ (KN5.H n p).ECCAt (n + 1) :=
  KN5.exists_choosable_not_ecc hn

open SimpleGraph in
example {k : ℕ} (hk : 2 ≤ k) :
    ∃ (V : Type) (iF : Fintype V) (iD : DecidableEq V) (G : SimpleGraph V)
      (iA : DecidableRel G.Adj), @Choosable V iF iD G iA k ∧ ¬ @ECCAt V iF iD G iA k :=
  KN5.exists_choosable_not_ecc_of_two_le hk
```

# Where the paper's `n ≥ 1` goes wrong

The hypothesis `2 ≤ n` above is not an artifact of the formalization. Lemmas 7 and 10 are printed
"for all `n ≥ 1`", and at `n = 1` — list size `2` — they are false, as is Lemma 9. There is no
admissible `p` at all, so $`H_2` is not defined; and for any `p` whatsoever the vertex $`v_1` is
joined to both ends of the single edge of $`K_{1,1}`, putting a triangle in $`H_2` and reversing
Lemma 7's inequality. {ref "findings"}[The findings chapter] gives the three failures with their
machine-checked witnesses.

This costs the paper nothing, because list size `2` has a witness of its own: $`\theta_{2,2,4}` is
`2`-choosable by Rubin's theorem, and is not enumeratively chromatic-choosable at `2` by the paper's
own Figure 2. Both were proved here long before Section 5 was, on the way to Theorem 2 —

```lean
open SimpleGraph ListColoring in
example : (theta 2).Choosable 2 ∧ ¬ (theta 2).ECCAt 2 :=
  choosable_and_not_ecc_theta 2 (by omega)
```

— and that is exactly the `k = 2` case of the statement two blocks above.

# A note on the arithmetic

One small thing worth recording, because it is a recurring trap. The proof needs that
`a * n + c = b * n + d` with `c, d < n` forces `a = b` and `c = d`. This is exactly the uniqueness
of division with remainder, and it is *not* something `omega` can do: `a * n` is nonlinear, with
both factors variable, and `omega` handles only linear integer arithmetic. The fix is to go through
`Nat.div` and `Nat.mod` explicitly rather than to look for a stronger tactic.
